using CyberPhysicalSurrogates
using CyberPhysicalFalsify
using FalconInterfaces
using FalconStrategies
using SignalTemporalLogic

minmax_tanh = x -> (tanh(x) + 1 )/2

X = reduce(vcat, [rand(3, 101), reshape([x.^1.001 for x in 1:101], 1, :), reshape([(x+.001).^1.01 for x in 1:101], 1, :)])

ϕCC1 = @formula ◊(1:101, x_t -> (x_t[5] - x_t[4] < 40))

ϕCC2 = @formula □(1:71, ◊(1:31, x_t -> (x_t[5] - x_t[4] > 15)))

ϕCC3_1 = @formula □(1:21, x_t -> (x_t[2] - x_t[1] < 20))
ϕCC3_2 = @formula ◊(1:21, x_t -> (x_t[5] - x_t[4] > 40))
ϕCC3 = @formula □(1:81, ϕCC3_1 || ϕCC3_2)

ϕCC4 = @formula □(1:66, ◊(1:31, □(1:6, x_t -> (x_t[5] - x_t[4] > 8))))

ϕCC5_1 = @formula □(1:6, x_t -> (x_t[2] - x_t[1] > 9))
ϕCC5_2 = @formula □(6:21, x_t -> (x_t[5] - x_t[4] > 9))
ϕCC5 = @formula □(1:73, ◊(1:9, !ϕCC5_1 || ϕCC5_2))

ϕCCx_1 = @formula □(1:51, x_t -> (x_t[2] - x_t[1] > 7.5))
ϕCCx_2 = @formula □(1:51, x_t -> (x_t[3] - x_t[2] > 7.5))
ϕCCx_3 = @formula □(1:51, x_t -> (x_t[4] - x_t[3] > 7.5))
ϕCCx_4 = @formula □(1:51, x_t -> (x_t[5] - x_t[4] > 7.5))
ϕCCx = @formula ϕCCx_1 && ϕCCx_2 && ϕCCx_3 && ϕCCx_4

ϕCC1(X)
ϕCC2(X)
ϕCC3(X)
ϕCC4(X)
ϕCC5(X)
ϕCCx(X)

ρ(X, ϕCC1)
ρ(X, ϕCC2)
ρ(X, ϕCC3)
ρ(X, ϕCC4)
ρ(X, ϕCC5)
ρ(X, ϕCCx)


∇ρ(X, ϕCC1)
∇ρ(X, ϕCC2)
∇ρ(X, ϕCC3)
∇ρ(X, ϕCC4)
∇ρ(X, ϕCC5)
∇ρ(X, ϕCCx)


@benchmark ϕCC1(X)
# BenchmarkTools.Trial: 10000 samples with 142 evaluations per sample.
#  Range (min … max):  699.437 ns …  82.469 μs  ┊ GC (min … max): 0.00% … 98.51%
#  Time  (median):     805.000 ns               ┊ GC (median):    0.00%
#  Time  (mean ± σ):   848.681 ns ± 989.162 ns  ┊ GC (mean ± σ):  1.84% ±  1.68%

#           █ ▂                                                    
#   ▂▂▂▂▂▃▆▆███▆▆▅▄▃▃▃▃▂▂▂▂▂▂▂▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁ ▂
#   699 ns           Histogram: frequency by time         1.32 μs <

#  Memory estimate: 320 bytes, allocs estimate: 9.

@benchmark ϕCC2(X)
# BenchmarkTools.Trial: 10000 samples with 160 evaluations per sample.
#  Range (min … max):  647.225 ns … 49.806 μs  ┊ GC (min … max):  0.00% … 97.33%
#  Time  (median):     805.666 ns              ┊ GC (median):     0.00%
#  Time  (mean ± σ):     1.035 μs ±  2.095 μs  ┊ GC (mean ± σ):  17.03% ±  8.22%

#    ▁█▇█▇▅▄                                                      
#   ▃████████▆▅▄▃▃▃▂▂▂▂▂▂▁▂▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁ ▂
#   647 ns          Histogram: frequency by time         2.32 μs <

#  Memory estimate: 3.09 KiB, allocs estimate: 67.


@benchmark ϕCC3(X)
# BenchmarkTools.Trial: 2310 samples with 1 evaluation per sample.
#  Range (min … max):  1.774 ms …  10.635 ms  ┊ GC (min … max): 0.00% … 80.77%
#  Time  (median):     2.033 ms               ┊ GC (median):    0.00%
#  Time  (mean ± σ):   2.160 ms ± 578.819 μs  ┊ GC (mean ± σ):  2.87% ±  7.98%

#     ▄█▃                                                        
#   ▄▇███▇▆▄▄▃▃▃▃▃▂▂▂▂▂▂▂▂▂▂▂▂▁▂▂▂▁▂▁▁▁▁▁▁▁▁▁▁▁▁▁▂▁▁▁▁▁▁▁▁▁▂▂▂▂ ▃
#   1.77 ms         Histogram: frequency by time         5.7 ms <

#  Memory estimate: 1.11 MiB, allocs estimate: 29484.


@benchmark ϕCC4(X)
# BenchmarkTools.Trial: 10000 samples with 1 evaluation per sample.
#  Range (min … max):   8.974 μs … 51.357 μs  ┊ GC (min … max): 0.00% … 0.00%
#  Time  (median):     10.976 μs              ┊ GC (median):    0.00%
#  Time  (mean ± σ):   11.175 μs ±  2.081 μs  ┊ GC (mean ± σ):  0.00% ± 0.00%

#   ▅▆▆▆▆▆▅▄▆▇████▇▅▄▃▂▂▁▁▁  ▁                                  ▃
#   █████████████████████████████████▇▇█▇██▇▇▅▇▇▅▅▅▅▆▆▅▆▇▇▇██▆▇ █
#   8.97 μs      Histogram: log(frequency) by time      19.4 μs <

#  Memory estimate: 10.84 KiB, allocs estimate: 253.


@benchmark ϕCC5(X)
# BenchmarkTools.Trial: 10000 samples with 1 evaluation per sample.
#  Range (min … max):  64.011 μs …   7.678 ms  ┊ GC (min … max): 0.00% … 98.00%
#  Time  (median):     79.214 μs               ┊ GC (median):    0.00%
#  Time  (mean ± σ):   85.847 μs ± 137.252 μs  ┊ GC (mean ± σ):  3.72% ±  2.38%

#       ▁▁▁▂ ▅▄▆█▅▃                                               
#   ▄▇▇█████████████▆▆▅▄▄▅▅▅▄▄▄▅▆▅▄▃▃▂▂▂▂▁▂▂▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁ ▃
#   64 μs           Histogram: frequency by time          137 μs <

#  Memory estimate: 78.70 KiB, allocs estimate: 1825


@benchmark ϕCCx(X)
# BenchmarkTools.Trial: 10000 samples with 10 evaluations per sample.
#  Range (min … max):  1.242 μs …   4.550 μs  ┊ GC (min … max): 0.00% … 0.00%
#  Time  (median):     1.471 μs               ┊ GC (median):    0.00%
#  Time  (mean ± σ):   1.523 μs ± 202.701 ns  ┊ GC (mean ± σ):  0.00% ± 0.00%

#          ▂▇█▇▇█▆▅▁                                             
#   ▂▃▃▃▃▄▆█████████▆▅▆▅▅▃▃▃▂▂▂▂▂▃▂▂▂▂▂▂▂▂▂▂▂▂▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁ ▃
#   1.24 μs         Histogram: frequency by time        2.32 μs <

#  Memory estimate: 1.17 KiB, allocs estimate: 31.




@benchmark ρ(X, ϕCC1)
# BenchmarkTools.Trial: 10000 samples with 6 evaluations per sample.
#  Range (min … max):  4.934 μs …  2.094 ms  ┊ GC (min … max):  0.00% … 99.27%
#  Time  (median):     6.580 μs              ┊ GC (median):     0.00%
#  Time  (mean ± σ):   8.905 μs ± 37.012 μs  ┊ GC (mean ± σ):  14.10% ±  3.67%

#     ▁▂▄▄▅▅█▇▂                                                 
#   ▃██████████▇▆▅▄▄▄▃▃▂▂▂▂▂▂▂▂▄▅▄▅▄▄▄▄▄▃▂▂▂▂▂▂▂▂▂▂▂▁▂▁▁▁▁▁▁▁▁ ▃
#   4.93 μs        Histogram: frequency by time          15 μs <

#  Memory estimate: 20.02 KiB, allocs estimate: 614.

@benchmark ρ(X, ϕCC2)
# BenchmarkTools.Trial: 10000 samples with 1 evaluation per sample.
#  Range (min … max):   86.443 μs …  13.160 ms  ┊ GC (min … max):  0.00% … 98.03%
#  Time  (median):     107.989 μs               ┊ GC (median):     0.00%
#  Time  (mean ± σ):   141.703 μs ± 343.108 μs  ┊ GC (mean ± σ):  16.43% ±  6.98%

#     ▂▆██▇▅▃▁                                                     
#   ▂▄████████▇▆▄▄▃▃▃▂▂▂▂▂▂▂▁▁▁▂▂▂▂▂▃▂▂▂▂▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁ ▂
#   86.4 μs          Histogram: frequency by time          266 μs <

#  Memory estimate: 426.81 KiB, allocs estimate: 9451.

@benchmark ρ(X, ϕCC3)
# BenchmarkTools.Trial: 10000 samples with 1 evaluation per sample.
#  Range (min … max):  192.289 μs …  12.928 ms  ┊ GC (min … max):  0.00% … 96.63%
#  Time  (median):     235.642 μs               ┊ GC (median):     0.00%
#  Time  (mean ± σ):   297.980 μs ± 450.626 μs  ┊ GC (mean ± σ):  14.81% ±  9.50%

#   █▆▄▃▁▁                                                        ▁
#   ██████▆▅▄▁▃▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▄▅ █
#   192 μs        Histogram: log(frequency) by time        3.9 ms <

#  Memory estimate: 714.67 KiB, allocs estimate: 18638.

@benchmark ρ(X, ϕCC4)
# BenchmarkTools.Trial: 3235 samples with 1 evaluation per sample.
#  Range (min … max):  1.129 ms …  13.089 ms  ┊ GC (min … max):  0.00% … 87.09%
#  Time  (median):     1.311 ms               ┊ GC (median):     0.00%
#  Time  (mean ± σ):   1.541 ms ± 896.605 μs  ┊ GC (mean ± σ):  11.60% ± 15.04%

#   ▆██▆▅▄▃▁▂▁                                                  ▁
#   ████████████▇▇▇▆▅▅▄▃▁▄▁▁▁▃▁▃▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▇▇██▆▇▄▇█▆ █
#   1.13 ms      Histogram: log(frequency) by time      5.75 ms <

#  Memory estimate: 3.07 MiB, allocs estimate: 68120.

@benchmark ρ(X, ϕCC5)
# BenchmarkTools.Trial: 3235 samples with 1 evaluation per sample.
#  Range (min … max):  1.129 ms …  13.089 ms  ┊ GC (min … max):  0.00% … 87.09%
#  Time  (median):     1.311 ms               ┊ GC (median):     0.00%
#  Time  (mean ± σ):   1.541 ms ± 896.605 μs  ┊ GC (mean ± σ):  11.60% ± 15.04%

#   ▆██▆▅▄▃▁▂▁                                                  ▁
#   ████████████▇▇▇▆▅▅▄▃▁▄▁▁▁▃▁▃▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▇▇██▆▇▄▇█▆ █
#   1.13 ms      Histogram: log(frequency) by time      5.75 ms <

#  Memory estimate: 3.07 MiB, allocs estimate: 68120.


@benchmark ρ(X, ϕCCx)
# BenchmarkTools.Trial: 10000 samples with 4 evaluations per sample.
#  Range (min … max):   7.313 μs …  3.269 ms  ┊ GC (min … max):  0.00% … 99.31%
#  Time  (median):      9.618 μs              ┊ GC (median):     0.00%
#  Time  (mean ± σ):   13.136 μs ± 57.779 μs  ┊ GC (mean ± σ):  14.71% ±  3.67%

#          ▇█▄                                                   
#   ▂▄▆▆█▅█████▅▄▄▃▂▂▂▂▂▂▂▂▁▁▁▁▁▁▂▂▃▄▆▄▃▃▂▃▂▂▂▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁▁ ▂
#   7.31 μs         Histogram: frequency by time        21.9 μs <

#  Memory estimate: 37.77 KiB, allocs estimate: 854.


@benchmark ∇ρ(X, ϕCC1)


@benchmark ∇ρ(X, ϕCC2)


@benchmark ∇ρ(X, ϕCC3)
@benchmark ∇ρ(X, ϕCC4)
@benchmark ∇ρ(X, ϕCC5)
@benchmark ∇ρ(X, ϕCCx)


@code_warntype ϕCC1(X)
@code_warntype ϕCC2(X)
@code_warntype ϕCC3(X)
@code_warntype ϕCC4(X)
@code_warntype ϕCC5(X)
@code_warntype ϕCCx(X)

@code_warntype ρ(X, ϕCC1)
@code_warntype ρ(X, ϕCC2)
@code_warntype ρ(X, ϕCC3)
@code_warntype ρ(X, ϕCC4)
@code_warntype ρ(X, ϕCC5)
@code_warntype ρ(X, ϕCCx)


@code_warntype ρ(X, ϕCC1)
@code_warntype ρ(X, ϕCC2)
@code_warntype ρ(X, ϕCC3)


@code_warntype ∇ρ(X, ϕCC1)
@code_warntype ∇ρ(X, ϕCC2)
@code_warntype ∇ρ(X, ϕCC3)
