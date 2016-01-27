# MultiLinearMaps
A Mathematica package to compose multilinear maps with named input and output spaces. 
Useful for avoiding index bookkeeping in quantum information theory calculations.

Use case:
Suppose M1 and M2 are two linear maps, M1 taking the vector space V_A otimes V_B to V_C and the second taking V_C otimes V_D to V_A. Composing M2 with M1 gives a new map from V_A otimes V_B otimes V_D to V_A. Given representatives of M1 and M2, we'd like to compute the composition map. And then compose the result with M3, and so on.

Each map is represented by an array/tensor of coefficients, so the calculation is just one of tensor contraction, which can be mapped to matrix multiplication. However, it is cumbersome to manually keep track of which indices are associated with what systems. Imposing a fixed system-tensor index correspondence also breaks down when, as in the example, systems come and go. MultiLinearMaps is meant to handle precisely this bookkeeping.  
