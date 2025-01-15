# Formalising Tate’s Thesis

This repository contains all of the Lean code written as a part of the "Formalising Tate’s Thesis" dissertation.

The code uses the statemetns and definition from the mathlib library, as well as the following repository:
https://github.com/smmercuri/adele-ring_locally-compact


## ContinuousAddChar.lean

The file ContinuousAddChar contains the definition of a continuous additive character and all of the related API. This defintion allows us to define the Pontryagin dual as a continuous additive character.

## GlobalNorm.lean

This file first defined the norms on the infinite and finite adeles and then uses those definitions to define a norm on the adeles. It's worth noting the norm is only well defined on the ideles, however we keep the general definition as it might simplify work later on.

## SetZ.lean

This file define the set $$Z$$ of functions for which the main theorem is defined.

## IsoAdeleDual.lean

This file is not finished yet. The goal is to define an isomorphism between the adele ring and it's Pontryagin dual (as additive groups).

## MainTheorem.lean

This file is not finished yet. The goal is to state and prove the main theorem. Currently the file contains a definition of the zeta function and the statement of the functional equation. However, the characters are defined over the ideles rather than their quotient by $$K$$.