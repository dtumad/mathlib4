module

import Aesop.Frontend.Attribute
import all Mathlib.Tactic.Linter.Whitespace
import Mathlib.Tactic.Linter.Style
import Mathlib.Init

set_option linter.style.whitespace true

/--
warning: missing space in the source

This part of the code
  'example: True'
should be written as
  'example : True'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
-/
#guard_msgs in
example: True := trivial

-- Constructs that are ignored by the linter, and (former) false positives.
section noFalsePositives

-- Explicit name literals: used to error (and the suggested replacement is invalid syntax).
structure foo (name: Lean.Name) where

#guard_msgs in
def bar (_param : List (foo ``String)) := 1

-- This example would trigger the linter if we did not special case
-- `where` in `Mathlib.Linter.Style.CommandStart.getUnlintedRanges`.
/-- A -/
example := aux
where
  /-- A -/
  aux : Unit := ()

-- For structure fields, all field definitions are linted.
-- TODO: currently, only the first field is linted
/--
warning: extra space in the source

This part of the code
  'field1     : Nat'
should be written as
  'field1 : Nat'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
-/
#guard_msgs in
structure A where
  field1     : Nat
  field2 : Nat

-- TODO: this is not linted yet!
structure B where
  field1 : Nat
  field2     : Nat

-- TODO: this is not linted yet!
structure C where
  field1 :     Nat
  field2     : Nat

-- Note that the linter does not attempt to recognise or respect manual alignment of fields:
-- this is often brittle and should usually be removed.
/--
warning: extra space in the source

This part of the code
  'field1    :  '
should be written as
  'field1 : Nat'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
-/
#guard_msgs in
structure D where
  field1    :     Nat
  field2    : Nat

-- This also applies to consecutive declarations.
/--
warning: declaration uses `sorry`
---
warning: extra space in the source

This part of the code
  'instance   {R}'
should be written as
  'instance {R} :'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
-/
#guard_msgs in
instance   {R} : Add R := sorry

-- TODO: right now, defining a second private `Add` instance causes an error
-- Once the fix for lean4#11385 lands in mathlib; revert this to an `Add` instance
/--
warning: declaration uses `sorry`
---
warning: extra space in the source

This part of the code
  'instance   {R}'
should be written as
  'instance {R} :'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
-/
#guard_msgs in
instance   {R} : Sub R := sorry

-- Strings are ignored by the linter.
variable (a : String := "  ")

-- The linter skips double-quoted names.
variable (d : Lean.Name := ``Nat) in open Nat

-- Code inside `run_cmd` is not checked at all.
run_cmd
  for _ in [0] do
    let _ ← `(
      end)

def Card : Type → Nat := fun _ => 0

/-- Symbols for use by all kinds of grammars. -/
inductive Symbol (T N : Type)
  /-- Terminal symbols (of the same type as the language) -/
  | terminal (t : T) : Symbol T N
  /-- Nonterminal symbols (must not be present when the word being generated is finalized) -/
  | nonterminal (n : N) : Symbol T N
deriving
  DecidableEq, Repr

-- embedded comments do not cause problems!
#guard_msgs in
open Nat in -- hi
example : True := trivial

-- embedded comments do not cause problems!
#guard_msgs in
open Nat in
 -- hi
example : True := trivial

-- embedded comments do not cause problems!
#guard_msgs in
open Nat in
  -- hi
example : True := trivial

structure X where
  /-- A doc -/
  x : Nat

open Nat in /- hi -/
example : True := trivial

-- The notation `0::[]` disables the linter
variable (h : 0::[] = [])

/-- A doc string -/
-- comment
example : True := trivial

-- Test that `Prop` and `Type` that are not escaped with `«...»` do not cause problems.
def Prop.Hello := 0
def Type.Hello := 0

/--
warning: extra space in the source

This part of the code
  'F  : True'
should be written as
  'F : True'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
-/
#guard_msgs in
lemma F  : True := trivial

namespace List

variable {α β : Type} (r : α → α → Prop) (s : β → β → Prop)

-- The two infix are needed.  They "hide" a `quotPrecheck`
local infixl:50 " ≼ " => r
-- The two infix are needed.  They "hide" a `quotPrecheck`
local infixl:50 " ≼ " => s

/--
warning: The `whitespace` linter had some parsing issues: feel free to silence it and report this error!

Note: This linter can be disabled with `set_option linter.style.whitespace.verbose false`
-/
#guard_msgs in
set_option linter.style.whitespace.verbose true in
example {a : α} (_ : a ≼ a) : 0 = 0 := rfl

end List

end noFalsePositives

-- Miscellaneous constructs: variable, include, omit statements; aesop rulesets
section misc

variable [h : Add Nat] [Add Nat]

/--
warning: extra space in the source

This part of the code
  'variable    [ h'
should be written as
  'variable [h :'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
---
warning: extra space in the source

This part of the code
  '[ h  '
should be written as
  '[h : Add'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
---
warning: extra space in the source

This part of the code
  'h    : Add'
should be written as
  '[h : Add'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
---
warning: extra space in the source

This part of the code
  'Nat   ] ['
should be written as
  'Nat] [Add'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
---
warning: extra space in the source

This part of the code
  '[ Add'
should be written as
  '[Add Nat]'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
-/
#guard_msgs in
variable    [ h    : Add Nat   ] [ Add Nat]

/--
warning: extra space in the source

This part of the code
  'omit  [h :'
should be written as
  'omit [h :'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
---
warning: extra space in the source

This part of the code
  'Nat]  [Add'
should be written as
  ' [Add'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
-/
#guard_msgs in
omit  [h : Add Nat]  [Add Nat]

-- Include statements are not linted.
include     h

set_option linter.overlappingInstances false in
/--
warning: extra space in the source

This part of the code
  '@[aesop  (rule_sets'
should be written as
  '@[aesop (rule_sets'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
-/
#guard_msgs in
@[aesop  (rule_sets := [builtin]) safe apply] example : True := trivial

end misc

/--
warning: 'section' starts on column 1, but all commands should start at the beginning of the line.

Note: This linter can be disabled with `set_option linter.style.whitespace false`
-/
#guard_msgs in
 section

/--
warning: extra space in the source

This part of the code
  'example    : True'
should be written as
  'example : True'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
-/
#guard_msgs in
example    : True := trivial

-- Additional spaces after the colon are not linted yet.
#guard_msgs in
example :     True := trivial

/--
warning: extra space in the source

This part of the code
  'example  :  True'
should be written as
  'example : True'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
-/
#guard_msgs in
example  :  True :=trivial

/--
warning: missing space in the source

This part of the code
  '(a: Nat)'
should be written as
  '(a : Nat)'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
-/
#guard_msgs in
variable (a: Nat)

/--
warning: missing space in the source

This part of the code
  '(_a: Nat)'
should be written as
  '(_a : Nat)'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
-/
#guard_msgs in
example (_a: Nat) : True := trivial

/--
warning: missing space in the source

This part of the code
  '{a: Nat}'
should be written as
  '{a : Nat}'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
-/
#guard_msgs in
example {a: Nat} : a = a := rfl

/--
a
b
c
d -/
example (_a : Nat) (_b : Int) : True := trivial

/--
warning: missing space in the source

This part of the code
  ':Nat}'
should be written as
  ': Nat}'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
-/
#guard_msgs in
example {a :Nat} : a = a := rfl

/--
warning: extra space in the source

This part of the code
  'example  {a :Nat}'
should be written as
  'example {a :'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
---
warning: missing space in the source

This part of the code
  ':Nat}'
should be written as
  ': Nat}'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
-/
#guard_msgs in
example  {a :Nat} : a = a := rfl

/--
warning: Variable name `b` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _b

Note: This linter can be disabled with `set_option linter.unusedVariables false`
---
warning: missing space in the source

This part of the code
  'Nat}{b :'
should be written as
  'Nat} {b :'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
-/
#guard_msgs in
example {a : Nat}{b : Nat} : a = a := rfl

/--
warning: extra space in the source

This part of the code
  'Nat}  : a'
should be written as
  'Nat} : a ='


Note: This linter can be disabled with `set_option linter.style.whitespace false`
-/
#guard_msgs in
example {a : Nat}  : a = a := rfl

/--
warning: extra space in the source

This part of the code
  'alpha   ] {a'
should be written as
  'alpha] {a'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
-/
#guard_msgs in
example {alpha} [Neg alpha   ] {a : Nat} : a = a := rfl

/--
warning: extra space in the source

This part of the code
  'example  : True'
should be written as
  'example : True'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
-/
#guard_msgs in
/-- Check that doc/strings do not get removed as comments. -/
example  : True := trivial

-- Only the hypotheses segment of a declaration is linted: formatting inside the type, the value
-- or the proof is never reported, even when it differs from the pretty-printed version.
section headerOnly

-- A misformatted proof body on its own is not reported.
#guard_msgs in
example (n : Nat) : n = n := by
  have  h :n = n :=  rfl
  exact  h

-- Misformatting in the hypotheses is reported, and misformatting later in the proof is not.
/--
warning: missing space in the source

This part of the code
  '(n: Nat)'
should be written as
  '(n : Nat)'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
-/
#guard_msgs in
example (n: Nat) : n + 0 = n := by
  have h  :  n + 0 = n   := by   simp
  exact   h

-- A missing space just before the colon is reported; just after it, it is not.
/--
warning: missing space in the source

This part of the code
  'Nat): True'
should be written as
  'Nat) : True'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
-/
#guard_msgs in
example (_n : Nat): True := trivial

#guard_msgs in
example (_n : Nat) :True := trivial

-- Multi-byte characters before the reported position.
/--
warning: missing space in the source

This part of the code
  'γ)(_x :'
should be written as
  'γ) (_x'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
-/
#guard_msgs in
example {γ : Type} (_f : γ → γ)(_x : γ) : True := trivial

#guard_msgs in
example {γ : Type} (_f : ∀ _ : γ, γ) (_x : γ) :∀ _ : γ, True := fun _ ↦ trivial

-- Without a type, linting stops where the value starts.
/--
warning: missing space in the source

This part of the code
  '(n:Nat)'
should be written as
  '(n : Nat)'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
-/
#guard_msgs in
def wsNoType (n:Nat) :=  n +  1

#guard_msgs in
def wsNoType' (n : Nat) :=  n +  1

-- An unlinted node in the hypotheses is still skipped, and what follows it is still linted.
/--
warning: missing space in the source

This part of the code
  '0})(_n :'
should be written as
  '}) (_n'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
-/
#guard_msgs in
example (_s : {x : Nat // x = 0})(_n : Nat) : True := trivial

-- A header that spans several lines, followed by a misformatted proof.
#guard_msgs in
example (a : Nat)
    (b : Nat) : a + b = b + a := by
  rw  [Nat.add_comm]

-- Comments inside the proof.
/--
warning: extra space in the source

This part of the code
  '(a  : Nat)'
should be written as
  '(a : Nat)'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
-/
#guard_msgs in
example (a  : Nat) : a = a := by
  -- a  comment   with  spaces
  /- a block   comment -/
  rfl

-- The constructors of an inductive type are not linted.
/--
warning: missing space in the source

This part of the code
  '(n: Nat)'
should be written as
  '(n : Nat)'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
-/
#guard_msgs in
inductive WsInd (n: Nat) where
  | mk  : WsInd n
  | other   (m :Nat) : WsInd n

-- Nor are the fields of an instance.
/--
warning: extra space in the source

This part of the code
  'instance  wsInst'
should be written as
  'instance wsInst'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
-/
#guard_msgs in
instance  wsInst : Inhabited Nat where
  default  :=  0

-- A doc-string, then a misformatted header and proof.
/--
warning: extra space in the source

This part of the code
  'wsDoc  (n :'
should be written as
  'wsDoc (n :'


Note: This linter can be disabled with `set_option linter.style.whitespace false`
-/
#guard_msgs in
/-- A doc-string   with  spaces. -/
theorem wsDoc  (n : Nat) : n = n := by
  exact   rfl

end headerOnly

-- Unit tests for internal functions in the linter.
section internal

/--
info: #[srcNat: 12, srcPos: 12, fmtPos: 2, msg: extra space, length: 7
, srcNat: 4, srcPos: 4, fmtPos: 1, msg: extra space, length: 3
]
-/
#guard_msgs in
#eval
  let s := "example        f   g"
  let t := "example fg"
  Mathlib.Linter.parallelScan s t

/--
info: #[srcNat: 19, srcPos: 19, fmtPos: 21, msg: extra space, length: 1
, srcNat: 16, srcPos: 16, fmtPos: 19, msg: extra space, length: 2
, srcNat: 7, srcPos: 7, fmtPos: 12, msg: missing space, length: 1
]
-/
#guard_msgs in
#eval
  let s := "example  :   True :=trivial"
  let t := "example : True :=
    trivial"
  Mathlib.Linter.parallelScan s t

/--
info: #[srcNat: 4, srcPos: 4, fmtPos: 5, msg: missing space, length: 1
, srcNat: 2, srcPos: 2, fmtPos: 1, msg: extra space, length: 1
]
-/
#guard_msgs in
#eval
  let l := "hac d"
  let m := "h  acd"
  Mathlib.Linter.parallelScan l m

-- Starting from `c` (due to the `"d ef gh".length` input), form a "window" of successive sizes
-- `1, 2,..., 6`.  The output is trimmed and contains only full words, even partially overlapping
-- with the given lengths.
#guard Mathlib.Linter.Style.Whitespace.mkWindow "ab cd ef gh" "d ef gh".length 1 == "cd"
#guard Mathlib.Linter.Style.Whitespace.mkWindow "ab cd ef gh" "d ef gh".length 2 == "cd"
#guard Mathlib.Linter.Style.Whitespace.mkWindow "ab cd ef gh" "d ef gh".length 3 == "cd ef"
#guard Mathlib.Linter.Style.Whitespace.mkWindow "ab cd ef gh" "d ef gh".length 4 == "cd ef"
#guard Mathlib.Linter.Style.Whitespace.mkWindow "ab cd ef gh" "d ef gh".length 5 == "cd ef"
#guard Mathlib.Linter.Style.Whitespace.mkWindow "ab cd ef gh" "d ef gh".length 6 == "cd ef gh"

end internal
