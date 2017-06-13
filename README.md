# MultiLinearMaps
A Mathematica package to compose multilinear maps with named input and output spaces. 
Useful for avoiding index bookkeeping in quantum information theory calculations.

Use case:
---------
Suppose M1 and M2 are two linear maps, M1 taking the vector space V_A otimes V_B to V_C and the second taking V_C otimes V_D to V_A. Composing M2 with M1 gives a new map from V_A otimes V_B otimes V_D to V_A. Given representatives of M1 and M2, we'd like to compute the composition map. And then compose the result with M3, and so on.

Each map is represented by an array/tensor of coefficients, so the calculation is just one of tensor contraction (which can be converted to matrix multiplication). However, it is cumbersome to manually keep track of which indices are associated with what systems. Imposing a fixed system-tensor index correspondence also breaks down when, as in the example, systems come and go. MultiLinearMaps is meant to handle precisely this bookkeeping. MultiLinearMaps also works with sparse arrays so that the whole thing doesn't break down at a small number of vector spaces.

For more on what MultiLinearMaps can do, see the Examples.nb notebook.

Installation:
-------------
To use the package, just download MultiLinearMaps.m somewhere Mathematica can find it and run

	<<MultiLinearMaps`

The particular version can be found in the variable $MLMVersion.

Related:
--------
See also [qitensor](http://www.stahlke.org/dan/qitensor/) for similar capabilities in python, as well as the earlier Mathematica package [qmatrix](http://www.timof.qipc.org/qmatrix/index.html). 

License
-------

[![license](https://img.shields.io/badge/license-New%20BSD-blue.svg)](http://en.wikipedia.org/wiki/BSD_licenses#3-clause_license_.28.22Revised_BSD_License.22.2C_.22New_BSD_License.22.2C_or_.22Modified_BSD_License.22.29)

You are free to use this software, with or without modification, provided that the conditions listed in the LICENSE.txt file are satisfied.
