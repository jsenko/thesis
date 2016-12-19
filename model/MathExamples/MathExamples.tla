----------------------------- MODULE MathExamples ----------------------------- 
EXTENDS Naturals
(***************************************************************************)
(* This is a TLA+ module that asserts some simple mathematical formulas    *)
(* to be true.  Each formula is preceded by the TLA+ keyword ASSUME,       *)
(* which means that it is to be taken as an assumption.  TLC checks that   *)
(* assumptions are valid, so it can be used to check the truth of          *)
(* formulas.                                                               *)
(*                                                                         *)
(* You can modify this file and run TLC to check your own formulas.        *)
(* However, observe the following constraints:                             *)
(*                                                                         *)
(*  - Use only the built-in TLA operators, which are listed in Tables 1    *)
(*    and 2 of the book.  (To use others, you either have to add their     *)
(*    definitions or the TLA+ statements that import their definitions     *)
(*    from other modules.)                                                 *)
(*                                                                         *)
(*  - The only variables you should use are bound variables--for example,  *)
(*    the ones introduced by existential quantification.                   *)
(*                                                                         *)
(*  - In your formulas, you can use natural numbers (0, 1, 2, ...  ),      *)
(*    strings like "abc", and the values a, b, c, d, e, f, and g, which    *)
(*    TLC will interpret as arbitrary values that are unequal to each      *)
(*    other and to any other value.                                        *)
(*                                                                         *)
(*  - Use only bounded quantifiers; TLC cannot handle the unbounded        *)
(*    quantifiers.  (It also cannot handle the unbounded CHOOSE operator). *)
(*                                                                         *)
(* This file contains a number of ASSUME statements.  They could be        *)
(* replaced by a single ASSUME that assumes the conjunction of all the     *)
(* formulas, but using separate ASSUMEs makes it easier to locate an       *)
(* error.                                                                  *)
(*                                                                         *)
(* Note: Table 8 tells you how to type all the symbols that do not have    *)
(* obvious ASCII equivalents.                                              *)
(***************************************************************************)


(*
 * Set theory
 *)

Nums == {1, 2, 3, 4, 5}

ASSUME 1 \in Nums

\*ASSUME 1 + 1 = 2

ASSUME {1, 2} = {2, 1}
(* Recursive operators not allowed
a ^^ b == IF b = 0 THEN 1 ELSE a * (a ^^ (b - 1))
*)
 
 (* choose must be from finite set *)
\*Next(x) == CHOOSE y \in Nat: y = x + 1

p | q == \E d \in 1..q : q = p * d

\*ASSUME 2 | 12

a %% b == CHOOSE c \in 0 .. (b - 1): \E x \in 0..a: a = x * b + c

ASSUME 12 %% 5 = 2

================================================================================