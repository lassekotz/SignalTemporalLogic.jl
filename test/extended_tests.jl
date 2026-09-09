# Extended unit tests for SignalTemporalLogic.jl
#
# This is a plain-Julia port of the coverage that used to live in the
# `runtests.jl` Pluto notebook, restructured into `@testset`s and extended so
# that every operator is exercised against **matrix-valued signals** (`n × T`
# `AbstractMatrix`, columns = time steps) in addition to the classic
# 1-D `Vector` signals.
#
# Tests assert the *intended* STL semantics. A handful of vector cases below
# currently fail because the package is mid-refactor: `get_interval` uses
# `size(x, 2)`, so `◊`/`□` *without an explicit interval* only inspect the
# first time step of a `Vector` signal. Those tests are marked with
#   # NOTE: WIP regression — vector ◊/□ with implicit interval
# and act as a guard until the refactor restores whole-trace semantics.

using Test
using SignalTemporalLogic
using SignalTemporalLogic: Trace, resolve_interval   # not exported

const STL = SignalTemporalLogic

# Scalar identity measure, matching the notebook.
μ(x) = x

# Measures for matrix signals (operate on a single time-step column).
mu1(xₜ)   = xₜ[1]            # first state component
mudiff(xₜ) = xₜ[1] - xₜ[2]   # ℝ² → ℝ

# 1-D reference signal (as in the notebook) and its `1 × T` matrix form.
const xvec = [-0.25, 0.0, 0.1, 0.6, 0.75, 1.0]
const xmat = reshape(copy(xvec), 1, :)

# A spread of 1-D trajectories (all length 6) exercised by the sweeps below.
# Each is deliberately a different qualitative shape.
const TRAJECTORIES = (
    increasing  = [-0.25, 0.0, 0.1, 0.6, 0.75, 1.0],   # monotone ↑, crosses 0
    decreasing  = [10.0, 5.0, 2.0, 0.5, -1.0, -4.0],   # monotone ↓, crosses 0
    oscillating = [1.0, -2.0, 3.0, -4.0, 5.0, -6.0],   # growing sign flips
    constant    = [2.5, 2.5, 2.5, 2.5, 2.5, 2.5],      # flat, always > 0
    pulse       = [0.0, 0.0, 5.0, 5.0, 0.0, 0.0],      # rectangular pulse
    alternating = [0.4, 0.6, 0.4, 0.6, 0.4, 0.6],      # straddles 0.5
)

# A spread of 2-D (n × T) trajectories, measured by `mudiff`.
const MD_TRAJECTORIES = (
    diverge  = [0.0 1 2 3 4 5;  0.0 -1 -2 -3 -4 -5],   # gap 0,2,4,6,8,10
    converge = [5.0 4 3 2 1 0; -5.0 -4 -3 -2 -1 0],    # gap 10,8,6,4,2,0
    crossing = [-2.0 -1 0 1 2 3;  2.0 1 0 -1 -2 -3],   # gap -4,-2,0,2,4,6
    parallel = [1.0 2 3 4 5 6;  0.0 1 2 3 4 5],        # gap 1,1,1,1,1,1
)

################################################################################
@testset "SignalTemporalLogic.jl" begin
################################################################################

#===============================================================================
                            Propositional logic
===============================================================================#
@testset "Propositional logic" begin
    @test (¬true, ¬false) == (false, true)

    @test (true  ∧ true)  == true
    @test (true  ∧ false) == false
    @test (false ∧ true)  == false
    @test (false ∧ false) == false

    @test (true  ∨ false) == true
    @test (false ∨ false) == false

    @test (false ⟹ false) == true
    @test (false ⟹ true)  == true
    @test (true  ⟹ false) == false
    @test (true  ⟹ true)  == true

    @test (true  ⟺ true)  == true
    @test (false ⟺ false) == true
    @test (true  ⟺ false) == false
end

#===============================================================================
                          @formula parsing / AST types
===============================================================================#
@testset "@formula parsing" begin
    @test isa(@formula(xₜ -> true), Atomic)
    @test isa(@formula(xₜ -> false), Atomic)
    @test isa(@formula(xₜ -> xₜ[1]), AtomicFunction)

    @test isa(@formula(xₜ -> μ(xₜ) > 0.5), Predicate)
    @test isa(@formula(xₜ -> xₜ > 0.5), Predicate)
    @test isa(@formula(xₜ -> μ(xₜ) < 0.5), FlippedPredicate)

    @test isa(@formula(xₜ -> ¬(μ(xₜ) > 0.5)), Negation)
    @test isa(@formula(xₜ -> !(xₜ > 0.5)), Negation)
    @test isa(@formula(¬(xₜ -> xₜ > 0.5)), Negation)

    @test isa(@formula((xₜ -> xₜ > 0.5) && (xₜ -> xₜ > 0)), Conjunction)
    @test isa(@formula((xₜ -> xₜ > 0.5) ∧ (xₜ -> xₜ > 0)), Conjunction)
    @test isa(@formula((xₜ -> xₜ > 0.5) || (xₜ -> xₜ > 0)), Disjunction)
    @test isa(@formula((xₜ -> xₜ > 0.5) ∨ (xₜ -> xₜ > 0)), Disjunction)
    @test isa(@formula((xₜ -> xₜ > 0.5) ⟹ (xₜ -> xₜ > 0)), Implication)
    @test isa(@formula((xₜ -> xₜ > 0.5) ⟺ (xₜ -> xₜ < 1.0)), Biconditional)
    @test isa(@formula((xₜ -> xₜ > 0.5) != (xₜ -> xₜ < 1.0)), Negation)

    @test isa(@formula(◊(xₜ -> xₜ > 0.5)), Eventually)
    @test isa(@formula(◊(3:5, xₜ -> xₜ > 0.5)), Eventually)
    @test isa(@formula(□(xₜ -> xₜ > 0.5)), Always)
    @test isa(@formula(□(1:5, xₜ -> xₜ > 0.5)), Always)
    @test isa(@formula(𝒰(xₜ -> xₜ > 0.5, xₜ -> xₜ < 0.5)), Until)

    # Real-valued closed intervals are permitted.
    @test isa(@formula(◊((0.0, 5.0), xₜ -> xₜ > 0.5)), Eventually)
    @test isa(@formula(□((0, 10), xₜ -> xₜ > 0.5)), Always)

    # Derived / combined formulas.
    @test isa((@formula(xₜ -> xₜ > 0)) ∧ (@formula(xₜ -> -xₜ > 0)), Function)
    @test isa((@formula(xₜ -> xₜ > 0)) ∨ (@formula(xₜ -> -xₜ > 0)), Function)

    # Interpolated / local variables in a predicate constant.
    let λ = 1234
        ϕ = @eval @formula s -> s > $λ
        @test ϕ.c == 1234
    end

    # AST helpers.
    neg_ex     = Expr(:(->), :xₜ, :(¬(μ(xₜ) > 0.5)))
    non_neg_ex = Expr(:(->), :xₜ, :(μ(xₜ) > 0.5))
    @test STL.strip_negation(neg_ex) == non_neg_ex
    @test STL.parse_formula(:(xₜ -> xₜ > 0.5)) isa Expr
end

#===============================================================================
                    Atomic operators (⊤ / ⊥) — value and robustness
===============================================================================#
@testset "Atomic ⊤ / ⊥" begin
    @test ⊤(xvec) == true
    @test ⊥(xvec) == false
    @test ρ(xvec, ⊤) == Inf
    @test ρ(xvec, ⊥) == -Inf
    @test ρ(xvec[1], ⊤) == Inf
    @test ρ̃(xvec, ⊤) == ρ(xvec, ⊤)

    ϕ_eq = @formula(xₜ -> xₜ == 0.5)
    @test ϕ_eq(0.5) && !ϕ_eq(1000)
end

#===============================================================================
                             VECTOR SIGNALS
===============================================================================#
@testset "Vector signals" begin
    x = xvec

    @testset "Predicate" begin
        ϕ = @formula xₜ -> μ(xₜ) > 0.5
        @test ϕ(x) == [xₜ > 0.5 for xₜ in x]
        @test ρ(x, ϕ) ≈ x .- 0.5
        @test ρ(x, @formula xₜ -> xₜ > 0.5) ≈ x .- 0.5      # without μ
        @test ρ̃(x, ϕ) == ρ(x, ϕ)
    end

    @testset "FlippedPredicate" begin
        ϕ = @formula xₜ -> xₜ < 0.5
        @test ϕ(x) == [xₜ < 0.5 for xₜ in x]
        @test ρ(x, ϕ) ≈ 0.5 .- x
    end

    @testset "Negation" begin
        ϕ = @formula xₜ -> ¬(xₜ > 0.5)
        @test ϕ(x) == [!(xₜ > 0.5) for xₜ in x]
        @test ρ(x, ϕ) ≈ -(x .- 0.5)
        @test ρ(x, @formula xₜ -> !(xₜ > 0.5)) ≈ -(x .- 0.5)
        # ¬ inside vs. outside the lambda agree.
        @test (@formula x -> ¬(x > 0))(x) == (@formula ¬(x -> x > 0))(x)
    end

    @testset "Conjunction" begin
        ϕ = @formula (xₜ -> μ(xₜ) > 0.5) && (xₜ -> μ(xₜ) > 0)
        @test ϕ(x) == false
        @test ρ(x, ϕ) ≈ min.(x .- 0.5, x)
        @test ρ̃(x, ϕ, 0) ≈ ρ(x, ϕ)
    end

    @testset "Disjunction" begin
        ϕ = @formula (xₜ -> μ(xₜ) > 0.5) || (xₜ -> μ(xₜ) > 0)
        @test ϕ(x) == true
        @test ρ(x, ϕ) ≈ max.(x .- 0.5, x)
        @test ρ̃(x, ϕ, 0) ≈ ρ(x, ϕ)
    end

    @testset "Implication" begin
        ϕ = @formula (xₜ -> μ(xₜ) > 0.5) ⟹ (xₜ -> μ(xₜ) > 0)
        @test ϕ(x) == trues(length(x))
        @test ρ(x, ϕ) ≈ max.(-(x .- 0.5), x)
    end

    @testset "Biconditional" begin
        ϕ = @formula (xₜ -> xₜ > 0.5) ⟺ (xₜ -> xₜ < 1.0)
        @test ϕ(x) == [(xₜ > 0.5) == (xₜ < 1.0) for xₜ in x]
        @test ρ(x, ϕ) ≈ min.(max.(-(x .- 0.5), 1.0 .- x), max.(x .- 0.5, -(1.0 .- x)))
    end

    @testset "Eventually (explicit interval)" begin
        ϕ = @formula ◊([3, 5], xₜ -> μ(xₜ) > 0.5)
        @test ϕ(x) == true
        @test ρ(x, ϕ) ≈ maximum(x[3:5] .- 0.5)          # == 0.25
        @test ρ(x, @formula ◊(3:3, xₜ -> xₜ > 0.5)) ≈ x[3] - 0.5
        @test robustness(x, ϕ) == ρ(x, ϕ)
    end

    @testset "Eventually (implicit interval)" begin
        # NOTE: WIP regression — vector ◊ with implicit interval
        ϕ = @formula ◊(xₜ -> xₜ > 0.5)
        @test ϕ(x) == true
        @test ρ(x, ϕ) ≈ maximum(x .- 0.5)               # == 0.5
    end

    @testset "Always (explicit interval)" begin
        @test (@formula □(1:2, xₜ -> xₜ > -0.5))(x) == true
        @test ρ(x, @formula □(1:2, xₜ -> xₜ > -0.5)) ≈ minimum(x[1:2] .+ 0.5)
        @test (@formula □(4:6, xₜ -> xₜ > 0.5))(x) == true
        @test ρ(x, @formula □(4:6, xₜ -> xₜ > 0.5)) ≈ minimum(x[4:6] .- 0.5)
    end

    @testset "Always (implicit interval)" begin
        # NOTE: WIP regression — vector □ with implicit interval
        xb = [1.0, -0.5, 2.0]
        @test (@formula □(xₜ -> xₜ > 0.0))(xb) == false
        @test ρ(xb, @formula □(xₜ -> xₜ > 0.0)) ≈ -0.5
        @test (@formula □(xₜ -> xₜ > -1.0))(xb) == true
        @test ρ(xb, @formula □(xₜ -> xₜ > -1.0)) ≈ 0.5

        ϕ = @formula □(xₜ -> xₜ > 0.5)
        @test robustness(x, ϕ) == ρ(x, ϕ)
        @test robustness(x, ϕ, 1) == ρ̃(x, ϕ)
        @test ρ̃(x, ϕ) == smooth_robustness(x, ϕ)
    end

    @testset "Until" begin
        # "ϕ until ψ": ∃i∈I. ψ(xᵢ) ∧ ∀j<i. ϕ(xⱼ). With no explicit interval the
        # whole trace is I. These are the notebook's assertions.
        # NOTE: WIP regression — implicit-interval 𝒰 uses `size(x,2)` (== 1 for a
        # vector), so it only inspects the first step and under-reports.
        _ϕ = @formula xₜ -> μ(xₜ) > 0
        _ψ = @formula xₜ -> -μ(xₜ) > 0
        U  = @formula 𝒰(_ϕ, _ψ)
        @test U([0.1, 1, 2, 3, -10, -9, -8]) == true    # ϕ holds through t=4, ψ at t=5
        @test U(x) == true
        @test U([0.001, 1, 2, 3, 4, 5, 6, 7, -8, -9, -10]) == true

        ϕ_until = @formula 𝒰(xₜ -> μ(xₜ) > 0, xₜ -> -μ(xₜ) > 0)
        x2 = [1.0, 2.0, 3.0, 4.0, -9.0, -8.0]
        @test ρ(x2, ϕ_until) == robustness(x2, ϕ_until)
        @test ρ̃(x2, ϕ_until, 0) == ρ(x2, ϕ_until)

        # Suffix-wise evaluation via `map`, from the notebook.
        function until_suffixes()
            ψ = @formula xₜ -> xₜ[1]
            φ = @formula xₜ -> xₜ[2]
            u = @formula 𝒰(ψ, φ)
            X = [[false, false], [false, false], [true, false], [true, false],
                 [true, true], [false, true], [false, true], [false, true]]
            return map(u, X)
        end
        @test until_suffixes() == Bool[0, 0, 1, 1, 1, 1, 1, 1]  # WIP regression

        # An explicit interval sidesteps the regression.
        @test ρ(x, @formula 𝒰(2:4, xₜ -> xₜ > 0, xₜ -> -xₜ > 0)) isa Real
    end

    @testset "map over time" begin
        ϕ = @formula xₜ -> μ(xₜ) > 0
        @test map(ϕ, x) == [ϕ(x[t:end]) for t in eachindex(x)]
    end

    @testset "Gradients" begin
        ϕ_ev = @formula ◊([3, 5], xₜ -> μ(xₜ) > 0.5)
        g  = ∇ρ(x, ϕ_ev)
        g̃  = ∇ρ̃(x, ϕ_ev)
        @test size(g) == (1, length(x))
        @test g == [0.0 0.0 0.0 0.0 1.0 0.0]   # max robustness at t = 5
        @test size(g̃) == (1, length(x))
        @test all(isfinite, g̃)

        x2 = [1.0, 2.0, 3.0, 4.0, -9.0, -8.0]
        ϕ_until = @formula 𝒰(xₜ -> μ(xₜ) > 0, xₜ -> -μ(xₜ) > 0)
        @test size(∇ρ(x2, ϕ_until)) == (1, length(x2))
        @test size(∇ρ̃(x2, ϕ_until)) == (1, length(x2))
    end

    @testset "Combining formulas" begin
        ϕ₁ = @formula xₜ -> xₜ > 0
        ϕ₂ = @formula xₜ -> -xₜ > 0
        x_comb = [4, 3, 2, 1, 0, -1, -2, -3, -4]
        @test (ϕ₁ ∨ ϕ₂).(x_comb) == [v != 0 for v in x_comb]
        @test (ϕ₁ ∧ ϕ₂).(x_comb) == falses(length(x_comb))
    end

    @testset "README example" begin
        # "eventually the signal will be greater than 0.5"
        ϕ = @formula ◊(xₜ -> xₜ > 0.5)
        @test ϕ(x) == true                                # NOTE: WIP regression
        @test ρ(x, ϕ) ≈ 0.5                               # NOTE: WIP regression
    end
end

#===============================================================================
                      MATRIX SIGNALS — 1 state dimension (1 × T)
===============================================================================#
@testset "Matrix signals (1 × T)" begin
    x = xmat
    T = size(x, 2)
    col(t) = x[1, t]

    @testset "Predicate" begin
        ϕ = @formula xₜ -> mu1(xₜ) > 0.5
        @test ϕ(x) == (col(1) > 0.5)
        @test ρ(x, ϕ) ≈ col(1) - 0.5
        @test ρ̃(x, ϕ) == ρ(x, ϕ)
    end

    @testset "FlippedPredicate" begin
        ϕ = @formula xₜ -> mu1(xₜ) < 0.5
        @test ϕ(x) == (col(1) < 0.5)
        @test ρ(x, ϕ) ≈ 0.5 - col(1)
    end

    @testset "Negation" begin
        ϕ = @formula xₜ -> ¬(mu1(xₜ) > 0.5)
        @test ϕ(x) == !(col(1) > 0.5)
        @test ρ(x, ϕ) ≈ -(col(1) - 0.5)
    end

    @testset "Conjunction" begin
        ϕ = @formula (xₜ -> mu1(xₜ) > 0.5) && (xₜ -> mu1(xₜ) > 0.0)
        @test ϕ(x) == false
        @test ρ(x, ϕ) ≈ min(col(1) - 0.5, col(1))
    end

    @testset "Disjunction" begin
        ϕ = @formula (xₜ -> mu1(xₜ) > 0.5) || (xₜ -> mu1(xₜ) > 0.0)
        @test ϕ(x) == false
        @test ρ(x, ϕ) ≈ max(col(1) - 0.5, col(1))
    end

    @testset "Implication" begin
        ϕ = @formula (xₜ -> mu1(xₜ) > 0.5) ⟹ (xₜ -> mu1(xₜ) > 0.0)
        @test ϕ(x) == true
        @test ρ(x, ϕ) ≈ max(-(col(1) - 0.5), col(1))
    end

    @testset "Always" begin
        ϕ = @formula □(xₜ -> mu1(xₜ) > -0.5)
        @test ϕ(x) == true
        @test ρ(x, ϕ) ≈ minimum(x .+ 0.5)

        ϕ_int = @formula □(1:3, xₜ -> mu1(xₜ) > -0.5)
        @test ϕ_int(x) == true
        @test ρ(x, ϕ_int) ≈ minimum(x[1, 1:3] .+ 0.5)

        ϕ_bad = @formula □(xₜ -> mu1(xₜ) > 0.5)
        @test ϕ_bad(x) == false
        @test ρ(x, ϕ_bad) ≈ minimum(x .- 0.5)
        @test robustness(x, ϕ_bad) == ρ(x, ϕ_bad)
        @test ρ̃(x, ϕ_bad, 0) ≈ ρ(x, ϕ_bad)
        @test ρ̃(x, ϕ_bad) == smooth_robustness(x, ϕ_bad)
    end

    @testset "Eventually" begin
        ϕ = @formula ◊(xₜ -> mu1(xₜ) > 0.5)
        @test ϕ(x) == true
        @test ρ(x, ϕ) ≈ maximum(x .- 0.5)

        ϕ_int = @formula ◊(1:3, xₜ -> mu1(xₜ) > 0.5)
        @test ϕ_int(x) == false
        @test ρ(x, ϕ_int) ≈ maximum(x[1, 1:3] .- 0.5)
        @test ρ̃(x, ϕ_int, 0) ≈ ρ(x, ϕ_int)
    end

    @testset "Nested temporal" begin
        Xbig = Float64[1 2 3 4 5 6 7 8 9 10]
        ϕ = @formula □(1:3, ◊(1:2, xₜ -> mu1(xₜ) > 3.0))
        @test ϕ(Xbig) == false
        @test ρ(Xbig, ϕ) ≈ -1.0

        ϕ2 = @formula □(1:3, (xₜ -> mu1(xₜ) > 0.5) ⟹ ◊(1:3, xₜ -> mu1(xₜ) > 0.5))
        @test ϕ2(Xbig) == true
        @test ρ(Xbig, ϕ2) ≈ 2.5
    end

    @testset "Gradients" begin
        ϕ = @formula □(xₜ -> mu1(xₜ) > -0.5)
        g = ∇ρ(x, ϕ)
        @test size(g) == (1, T)
        @test g == [1.0 0.0 0.0 0.0 0.0 0.0]     # min robustness at t = 1
        @test all(isfinite, ∇ρ̃(x, ϕ))
    end

    @testset "Agreement with vector signal" begin
        # Pointwise predicates give the same first-step robustness either way.
        ϕv = @formula xₜ -> μ(xₜ) > 0.5
        ϕm = @formula xₜ -> mu1(xₜ) > 0.5
        @test ρ(xmat, ϕm) ≈ ρ(xvec, ϕv)[1]
    end
end

#===============================================================================
                MATRIX SIGNALS — multidimensional state (n × T)
===============================================================================#
@testset "Matrix signals (n × T)" begin
    # columns: x[1] - x[2] == 0, 0, 0, -1
    X = [1.0 2.0 3.0 4.0;
         1.0 2.0 3.0 5.0]
    diffs = X[1, :] .- X[2, :]

    @testset "Predicate on ℝ² → ℝ" begin
        ϕ = @formula xₜ -> mudiff(xₜ) > -2.0
        @test ϕ(X) == true
        @test ρ(X, ϕ) ≈ diffs[1] + 2.0
    end

    @testset "Negation / junctions" begin
        @test (@formula xₜ -> ¬(mudiff(xₜ) > 0.0))(X) == true
        @test ρ(X, @formula xₜ -> ¬(mudiff(xₜ) > 0.0)) ≈ -(diffs[1])

        c = @formula (xₜ -> mudiff(xₜ) > -5.0) && (xₜ -> mudiff(xₜ) < 5.0)
        @test c(X) == true
        @test ρ(X, c) ≈ min(diffs[1] + 5.0, 5.0 - diffs[1])

        d = @formula (xₜ -> mudiff(xₜ) > 0.0) || (xₜ -> mudiff(xₜ) < -3.0)
        @test d(X) == false
        @test ρ(X, d) ≈ max(diffs[1], -(diffs[1] + 3.0))
        @test robustness(X, d) == ρ(X, d)
    end

    @testset "Always / Eventually" begin
        alw = @formula □(xₜ -> mudiff(xₜ) > -2.0)
        @test alw(X) == true
        @test ρ(X, alw) ≈ minimum(diffs) + 2.0

        alw_bad = @formula □(xₜ -> mudiff(xₜ) > -0.5)
        @test alw_bad(X) == false
        @test ρ(X, alw_bad) ≈ minimum(diffs) + 0.5

        ev = @formula ◊(xₜ -> mudiff(xₜ) > -0.5)
        @test ev(X) == true
        @test ρ(X, ev) ≈ maximum(diffs) + 0.5

        ev_bad = @formula ◊(xₜ -> mudiff(xₜ) > 0.5)
        @test ev_bad(X) == false
        @test ρ(X, ev_bad) ≈ maximum(diffs) - 0.5
    end

    @testset "Automatic transmission example" begin
        speeds = Float64[114, 117, 100, 96, 92, 88, 108, 101, 118, 119]
        rpms   = Float64[4719, 4747, 4706, 4744, 4701, 4744, 4743, 4753, 4712, 4704]
        signals = permutedims(hcat(speeds, rpms))          # 2 × 10

        transmission = @formula □(1:10, x -> x[1] < 120) ∧ □(1:5, x -> x[2] < 4750)
        @test transmission(signals) == true
        @test ρ(signals, transmission) ≈ min(120 - maximum(speeds),
                                             4750 - maximum(rpms[1:5]))   # == 1.0

        violated = @formula □(1:10, x -> x[1] < 100) ∧ □(1:5, x -> x[2] < 4750)
        @test violated(signals) == false
    end

    @testset "Gradients" begin
        alw = @formula □(xₜ -> mudiff(xₜ) > -2.0)
        g = ∇ρ(X, alw)
        @test size(g) == (1, length(X))
        @test any(!iszero, g)
        @test all(isfinite, ∇ρ̃(X, alw))
    end
end

#===============================================================================
                     Vectorized robustness  (ρ_vec / ρ̃_vec)
===============================================================================#
@testset "Vectorized robustness" begin
    X = [1.0 2.0 3.0 4.0;
         1.0 2.0 3.0 5.0]
    diffs = X[1, :] .- X[2, :]

    @testset "Predicate over time" begin
        ϕ = @formula xₜ -> mudiff(xₜ) > -2.0
        v = ρ_vec(X, ϕ)
        @test v ≈ diffs .+ 2.0
        @test v[1] ≈ ρ(X, ϕ)
        @test ρ̃_vec(X, ϕ) == ρ_vec(X, ϕ)
    end

    @testset "Negation over time" begin
        ϕ = @formula xₜ -> ¬(mudiff(xₜ) > -2.0)
        @test ρ_vec(X, ϕ) ≈ -(diffs .+ 2.0)
    end

    @testset "Conjunction / Disjunction over time" begin
        c = @formula (xₜ -> mudiff(xₜ) > -5.0) && (xₜ -> mudiff(xₜ) < 5.0)
        @test ρ_vec(X, c) ≈ min.(diffs .+ 5.0, 5.0 .- diffs)

        d = @formula (xₜ -> mudiff(xₜ) > 0.0) || (xₜ -> mudiff(xₜ) < -3.0)
        @test ρ_vec(X, d) ≈ max.(diffs, -(diffs .+ 3.0))
    end

    @testset "Temporal operators pad with NaN" begin
        alw = @formula □(xₜ -> mudiff(xₜ) > -2.0)
        v = ρ_vec(X, alw)
        @test length(v) == size(X, 2)
        @test v[1] ≈ ρ(X, alw)
        @test all(isnan, v[2:end])

        ev = @formula ◊(xₜ -> mudiff(xₜ) > -0.5)
        w = ρ_vec(X, ev)
        @test w[1] ≈ ρ(X, ev)
        @test all(isnan, w[2:end])
    end
end

#===============================================================================
             Trajectory sweep — vector signals across many shapes
===============================================================================#
@testset "Trajectory sweep (vector)" begin
    for (name, x) in pairs(TRAJECTORIES)
        T = length(x)
        @testset "$name" begin
            # --- Predicate / FlippedPredicate: elementwise robustness --------
            @test ρ(x, @formula xₜ -> xₜ > 0.5) ≈ x .- 0.5
            @test ρ(x, @formula xₜ -> xₜ < 0.5) ≈ 0.5 .- x
            @test (@formula xₜ -> xₜ > 0.5)(x) == (x .> 0.5)

            # --- Negation is robustness negation ----------------------------
            ϕ = @formula xₜ -> xₜ > 0.3
            @test ρ(x, @formula xₜ -> ¬(xₜ > 0.3)) ≈ -ρ(x, ϕ)

            # --- Conjunction / Disjunction are min / max --------------------
            ϕ_and = @formula (xₜ -> xₜ > 0.0) && (xₜ -> xₜ > 1.0)
            ϕ_or  = @formula (xₜ -> xₜ > 0.0) || (xₜ -> xₜ > 1.0)
            @test ρ(x, ϕ_and) ≈ min.(x, x .- 1.0)
            @test ρ(x, ϕ_or)  ≈ max.(x, x .- 1.0)

            # --- De Morgan -------------------------------------------------
            @test ρ(x, @formula ¬((xₜ -> xₜ > 0.0) && (xₜ -> xₜ > 1.0))) ≈
                  ρ(x, @formula (xₜ -> ¬(xₜ > 0.0)) || (xₜ -> ¬(xₜ > 1.0)))

            # --- Always / Eventually over the whole (explicit) interval -----
            alw = @formula □(1:6, xₜ -> xₜ > 0.0)
            evt = @formula ◊(1:6, xₜ -> xₜ > 0.0)
            @test ρ(x, alw) ≈ minimum(x)
            @test ρ(x, evt) ≈ maximum(x)
            @test alw(x) == all(>(0.0), x)
            @test evt(x) == any(>(0.0), x)
            @test sign(ρ(x, alw)) == (alw(x) ? 1 : -1) || iszero(ρ(x, alw))
            @test sign(ρ(x, evt)) == (evt(x) ? 1 : -1) || iszero(ρ(x, evt))

            # --- ◊/□ duality ---------------------------------------------
            @test ρ(x, alw) ≈ -ρ(x, @formula ◊(1:6, xₜ -> ¬(xₜ > 0.0)))
            @test ρ(x, evt) ≈ -ρ(x, @formula □(1:6, xₜ -> ¬(xₜ > 0.0)))

            # --- robustness / smooth-robustness plumbing -------------------
            @test robustness(x, alw) == ρ(x, alw)
            @test ρ̃(x, alw, 0) ≈ ρ(x, alw)
            @test ρ̃(x, evt, 0) ≈ ρ(x, evt)
            @test ρ̃(x, alw, 1) <= ρ(x, alw) + 1e-8   # smoothmin under-estimates
            @test ρ̃(x, evt, 1) >= ρ(x, evt) - 1e-8   # smoothmax over-estimates

            # --- gradient shape ------------------------------------------
            @test size(∇ρ(float(x), evt)) == (1, T)
            @test all(isfinite, ∇ρ̃(float(x), evt))
        end
    end

    # --- Concrete per-trajectory expectations --------------------------------
    expected = (  # (□(1:6, >0) bool, ρ,  ◊(1:6, >0) bool, ρ)
        increasing  = (false, -0.25, true,  1.0),
        decreasing  = (false, -4.0,  true, 10.0),
        oscillating = (false, -6.0,  true,  5.0),
        constant    = (true,   2.5,  true,  2.5),
        pulse       = (false,  0.0,  true,  5.0),
        alternating = (true,   0.4,  true,  0.6),
    )
    for (name, x) in pairs(TRAJECTORIES)
        alw = @formula □(1:6, xₜ -> xₜ > 0.0)
        evt = @formula ◊(1:6, xₜ -> xₜ > 0.0)
        b□, r□, b◊, r◊ = expected[name]
        @testset "$name expected values" begin
            @test alw(x) == b□
            @test ρ(x, alw) ≈ r□
            @test evt(x) == b◊
            @test ρ(x, evt) ≈ r◊
        end
    end

    # --- Until across trajectories -----------------------------------------
    @testset "Until: positive-then-negative" begin
        U = @formula 𝒰(1:6, xₜ -> xₜ > 0, xₜ -> xₜ < 0)
        @test U(TRAJECTORIES.decreasing) == true    # 10,5,2,0.5 > 0 then -1 < 0
        @test U(TRAJECTORIES.oscillating) == true   # 1 > 0 then -2 < 0
        @test U(TRAJECTORIES.constant) == false     # never negative
        @test U(TRAJECTORIES.increasing) == true    # x₁ < 0, so satisfied vacuously at t=1
        for x in TRAJECTORIES
            @test ρ(x, U) == robustness(x, U)
        end
    end
end

#===============================================================================
           Trajectory sweep — same shapes as 1 × T matrix signals
===============================================================================#
@testset "Trajectory sweep (matrix 1 × T)" begin
    for (name, xv) in pairs(TRAJECTORIES)
        x = reshape(collect(xv), 1, :)
        T = size(x, 2)
        @testset "$name" begin
            # Predicate looks at the first column only.
            @test (@formula xₜ -> mu1(xₜ) > 0.0)(x) == (xv[1] > 0.0)
            @test ρ(x, @formula xₜ -> mu1(xₜ) > 0.0) ≈ xv[1]

            # Always / Eventually reduce over the whole trace.
            alw = @formula □(xₜ -> mu1(xₜ) > 0.0)
            evt = @formula ◊(xₜ -> mu1(xₜ) > 0.0)
            @test alw(x) == all(>(0.0), xv)
            @test evt(x) == any(>(0.0), xv)
            @test ρ(x, alw) ≈ minimum(xv)
            @test ρ(x, evt) ≈ maximum(xv)

            # Bounded interval agrees with the vector semantics.
            @test ρ(x, @formula □(1:6, xₜ -> mu1(xₜ) > 0.0)) ≈ minimum(xv)
            @test ρ(x, @formula ◊(1:6, xₜ -> mu1(xₜ) > 0.0)) ≈ maximum(xv)

            # Smooth robustness collapses to hard robustness at w = 0.
            @test ρ̃(x, alw, 0) ≈ ρ(x, alw)
            @test ρ̃(x, evt, 0) ≈ ρ(x, evt)
            @test robustness(x, alw) == ρ(x, alw)

            # Matrix result equals the vector result for these pointwise specs.
            @test ρ(x, alw) ≈ ρ(collect(xv), @formula □(1:6, xₜ -> xₜ > 0.0))
            @test ρ(x, evt) ≈ ρ(collect(xv), @formula ◊(1:6, xₜ -> xₜ > 0.0))

            @test size(∇ρ(x, alw)) == (1, T)
            @test all(isfinite, ∇ρ̃(x, evt))
        end
    end
end

#===============================================================================
          Trajectory sweep — multidimensional (n × T) matrix signals
===============================================================================#
@testset "Multidimensional trajectory sweep (n × T)" begin
    expected = (  # minimum gap, maximum gap
        diverge  = (0.0, 10.0),
        converge = (0.0, 10.0),
        crossing = (-4.0, 6.0),
        parallel = (1.0,  1.0),
    )
    for (name, X) in pairs(MD_TRAJECTORIES)
        T = size(X, 2)
        gaps = X[1, :] .- X[2, :]
        gmin, gmax = expected[name]
        @testset "$name" begin
            @test extrema(gaps) == (gmin, gmax)

            # Predicate on ℝ² → ℝ, first column.
            @test ρ(X, @formula xₜ -> mudiff(xₜ) > 0.0) ≈ gaps[1]
            @test (@formula xₜ -> mudiff(xₜ) > 0.0)(X) == (gaps[1] > 0.0)

            # Always / Eventually.
            alw = @formula □(xₜ -> mudiff(xₜ) > 0.0)
            evt = @formula ◊(xₜ -> mudiff(xₜ) > 0.0)
            @test ρ(X, alw) ≈ gmin
            @test ρ(X, evt) ≈ gmax
            @test alw(X) == (gmin > 0.0)
            @test evt(X) == (gmax > 0.0)

            # Bounded interval form.
            @test ρ(X, @formula □(1:6, xₜ -> mudiff(xₜ) > 0.0)) ≈ gmin
            @test ρ(X, @formula ◊(1:6, xₜ -> mudiff(xₜ) > 0.0)) ≈ gmax

            # Duality and negation.
            @test ρ(X, alw) ≈ -ρ(X, @formula ◊(xₜ -> ¬(mudiff(xₜ) > 0.0)))
            @test ρ(X, @formula xₜ -> ¬(mudiff(xₜ) > 0.0)) ≈ -gaps[1]

            # Conjunction / Disjunction over the first column.
            c = @formula (xₜ -> mudiff(xₜ) > -1.0) && (xₜ -> mudiff(xₜ) < 12.0)
            @test ρ(X, c) ≈ min(gaps[1] + 1.0, 12.0 - gaps[1])

            # Vectorized robustness: predicate over all time, temporal padded.
            @test ρ_vec(X, @formula xₜ -> mudiff(xₜ) > 0.0) ≈ gaps
            v = ρ_vec(X, alw)
            @test v[1] ≈ ρ(X, alw)
            @test all(isnan, v[2:end])

            # Plumbing.
            @test robustness(X, alw) == ρ(X, alw)
            @test ρ̃(X, alw, 0) ≈ ρ(X, alw)
            @test size(∇ρ(X, alw)) == (1, length(X))
            @test all(isfinite, ∇ρ̃(X, evt))
        end
    end

    @testset "cross-trajectory: eventually the gap opens up" begin
        ϕ = @formula ◊(xₜ -> mudiff(xₜ) > 5.0)
        @test ϕ(MD_TRAJECTORIES.diverge) == true
        @test ϕ(MD_TRAJECTORIES.converge) == true
        @test ϕ(MD_TRAJECTORIES.crossing) == true
        @test ϕ(MD_TRAJECTORIES.parallel) == false
    end
end

#===============================================================================
        Trace signals — (possibly non-equidistant) real-valued time stamps
===============================================================================#
# `Trace(x, t)` bundles an `n × T` signal with a length-`T` vector of sample
# times, so temporal operators can carry *real-valued* closed intervals
# `(a, b)` (seconds, say) instead of integer index ranges. Only the vectorized
# `ρ_vec` path dispatches on `Trace` (plus a `t_now` "evaluation time" argument);
# `ρ`, `ρ̃` and boolean evaluation do not accept a `Trace`.

# Compare NaN-padded robustness vectors (NaN positions must line up).
nan_eq(a, b) = length(a) == length(b) &&
    all(isnan(p) ? isnan(q) : p ≈ q for (p, q) in zip(a, b))

@testset "Trace signals" begin
    # mu1(col) = col[1] sweeps 0 … 5 across the six columns.
    X = Float64[0 1 2 3 4 5;
                0 0 0 0 0 0]
    uniform    = collect(0.0:1.0:5.0)
    nonuniform = [0.0, 0.5, 1.5, 2.0, 4.0, 9.0]

    @testset "Leaves & junctions ignore the time vector" begin
        for t in (uniform, nonuniform, [0.0, 2.0, 2.1, 2.2, 8.0, 100.0])
            tr = Trace(X, t)
            p  = @formula xₜ -> mu1(xₜ) > 1.5
            pf = @formula xₜ -> mu1(xₜ) < 4.5
            ng = @formula xₜ -> ¬(mu1(xₜ) > 1.5)
            cj = @formula (xₜ -> mu1(xₜ) > 0.5) && (xₜ -> mu1(xₜ) < 4.5)
            dj = @formula (xₜ -> mu1(xₜ) > 4.5) || (xₜ -> mu1(xₜ) < 0.5)
            @test ρ_vec(tr, p,  0.0) == ρ_vec(X, p)
            @test ρ_vec(tr, pf, 0.0) == ρ_vec(X, pf)
            @test ρ_vec(tr, ng, 3.0) == ρ_vec(X, ng)
            @test ρ_vec(tr, cj, 1.7) == ρ_vec(X, cj)
            @test ρ_vec(tr, dj, 0.0) == ρ_vec(X, dj)
        end
    end

    @testset "resolve_interval maps real time → sample indices" begin
        tr = Trace(X, nonuniform)                       # [0, .5, 1.5, 2, 4, 9]
        @test resolve_interval(tr, (@formula □((0.0, 2.0), xₜ -> mu1(xₜ) > 0)), 0.0) == 1:4
        @test resolve_interval(tr, (@formula □((0.0, 2.0), xₜ -> mu1(xₜ) > 0)), 0.5) == 2:4  # window [0.5, 2.5]
        @test resolve_interval(tr, (@formula ◊((1.0, 8.0), xₜ -> mu1(xₜ) > 0)), 0.0) == 3:5
        @test resolve_interval(tr, (@formula ◊((0.0, 100.0), xₜ -> mu1(xₜ) > 0)), 0.0) == 1:6
    end

    @testset "Always / Eventually over a real-time window" begin
        tr = Trace(X, nonuniform)
        children = X[1, :] .- 1.0                       # ρ of (mu1 > 1.0) per step
        alw = @formula □((0.0, 2.0), xₜ -> mu1(xₜ) > 1.0)
        evt = @formula ◊((0.0, 2.0), xₜ -> mu1(xₜ) > 1.0)

        I0 = resolve_interval(tr, alw, 0.0)             # 1:4
        @test ρ_vec(tr, alw, 0.0)[1] ≈ minimum(children[I0])
        @test ρ_vec(tr, evt, 0.0)[1] ≈ maximum(children[I0])

        I5 = resolve_interval(tr, alw, 0.5)             # 2:5
        @test ρ_vec(tr, alw, 0.5)[1] ≈ minimum(children[I5])
        @test ρ_vec(tr, evt, 0.5)[1] ≈ maximum(children[I5])

        # A wide-open interval reduces over the whole trace.
        wide = @formula ◊((0.0, 100.0), xₜ -> mu1(xₜ) > 1.0)
        @test ρ_vec(tr, wide, 0.0)[1] ≈ maximum(children)

        # Trailing entries are NaN-padded, never leaking into the valid prefix.
        v = ρ_vec(tr, alw, 0.0)
        @test length(v) == size(X, 2)
        @test !any(isnan, v[1:something(findfirst(isnan, v), length(v)+1)-1])
    end

    @testset "Equidistant Trace ≡ integer-index ρ_vec" begin
        # Times 0, dt, 2dt, …  ⇒  real interval (0, k·dt)  ≡  index range 1:(k+1).
        Xu = Float64[0 1 2 3 4 5 6 7;
                     0 0 0 0 0 0 0 0]
        dt = 0.25
        tr = Trace(Xu, collect(0.0:dt:(7dt)))
        alw_r = @formula □((0.0, 0.5), xₜ -> mu1(xₜ) > 1.0)   # covers indices 1:3
        evt_r = @formula ◊((0.0, 0.5), xₜ -> mu1(xₜ) > 1.0)
        @test resolve_interval(tr, alw_r, 0.0) == 1:3
        @test nan_eq(ρ_vec(tr, alw_r, 0.0), ρ_vec(Xu, @formula □(1:3, xₜ -> mu1(xₜ) > 1.0)))
        @test nan_eq(ρ_vec(tr, evt_r, 0.0), ρ_vec(Xu, @formula ◊(1:3, xₜ -> mu1(xₜ) > 1.0)))

        # Nested spec, matching the benchmarks.jl cross-check pattern.
        nest_i = @formula □(1:5, ◊(1:3, xₜ -> mu1(xₜ) > 1.0))
        nest_r = @formula □((0.0, 1.0), ◊((0.0, 0.5), xₜ -> mu1(xₜ) > 1.0))
        @test ρ_vec(tr, nest_r, 0.0)[1] ≈ ρ_vec(Xu, nest_i)[1]
    end

    @testset "Trace not accepted by ρ / ρ̃ / boolean eval" begin
        tr = Trace(X, uniform)
        ϕ = @formula □((0.0, 3.0), xₜ -> mu1(xₜ) > 1.0)
        @test_throws MethodError ρ(tr, ϕ)
        @test_throws MethodError ϕ(tr)
    end

    #---------------------------------------------------------------------------
    # Mirror of the multidimensional sweep, evaluated through a Trace.
    #---------------------------------------------------------------------------
    @testset "Multidimensional Trace sweep" begin
        md_uniform    = collect(0.0:1.0:5.0)
        md_nonuniform = [0.0, 0.5, 1.5, 2.0, 4.0, 9.0]
        for (name, Xmd) in pairs(MD_TRAJECTORIES)
            gaps = Xmd[1, :] .- Xmd[2, :]
            @testset "$name" begin
                for t in (md_uniform, md_nonuniform)
                    tr = Trace(Xmd, t)

                    # Predicate over time is the raw gap sequence, time-agnostic.
                    p = @formula xₜ -> mudiff(xₜ) > 0.0
                    @test ρ_vec(tr, p, 0.0) ≈ gaps
                    @test ρ_vec(tr, p, 0.0) == ρ_vec(Xmd, p)
                    @test ρ_vec(tr, (@formula xₜ -> ¬(mudiff(xₜ) > 0.0)), 0.0) ≈ -gaps

                    # Temporal ops: first entry = extremum over the resolved window.
                    ch  = gaps .+ 1.0                     # ρ of (mudiff > -1)
                    alw = @formula □((0.0, 2.0), xₜ -> mudiff(xₜ) > -1.0)
                    evt = @formula ◊((0.0, 2.0), xₜ -> mudiff(xₜ) > -1.0)
                    I = resolve_interval(tr, alw, 0.0)
                    @test ρ_vec(tr, alw, 0.0)[1] ≈ minimum(ch[I])
                    @test ρ_vec(tr, evt, 0.0)[1] ≈ maximum(ch[I])
                end

                # On the uniform grid the Trace result matches the plain matrix.
                tru = Trace(Xmd, md_uniform)
                alw_r = @formula □((0.0, 2.0), xₜ -> mudiff(xₜ) > -1.0)
                alw_i = @formula □(1:3, xₜ -> mudiff(xₜ) > -1.0)
                @test resolve_interval(tru, alw_r, 0.0) == 1:3
                @test nan_eq(ρ_vec(tru, alw_r, 0.0), ρ_vec(Xmd, alw_i))
            end
        end
    end
    @testset "ARCH-COMP24 sweep" begin
        
        #TODO: Write tests...
        
    end
end

#===============================================================================
                       Smooth min / max approximations
===============================================================================#
@testset "Smooth min / max" begin
    sm = [1.0, 2.0, 3.0, 4.0, 0.2]

    @test smoothmin(sm, 0) == minimum(sm)
    @test smoothmax(sm, 0) == maximum(sm)

    # Default weight W == 1.
    @test smoothmin(sm) == smoothmin(sm, 1)
    @test smoothmax(sm) == smoothmax(sm, 1)

    # Smooth min/max bracket the true extrema for finite positive weight.
    @test smoothmin(sm, 1) <= minimum(sm)
    @test smoothmax(sm, 1) >= maximum(sm)

    # Two-argument (scalar) form.
    @test smoothmin(3.0, 5.0, 0) == 3.0
    @test smoothmax(3.0, 5.0, 0) == 5.0
    @test smoothmin(3.0, 5.0, 1) ≈ smoothmin([3.0, 5.0], 1)

    # `robustness` dispatches on the positional weight.
    ϕ = @formula □(1:3, xₜ -> xₜ > -1.0)
    @test robustness(xvec, ϕ) == ρ(xvec, ϕ)
    @test robustness(xvec, ϕ, 1) == ρ̃(xvec, ϕ, 1)
end

################################################################################
end # @testset "SignalTemporalLogic.jl"
################################################################################
