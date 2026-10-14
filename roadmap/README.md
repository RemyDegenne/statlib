# Proposed design document template

This is a reference checklist, not a required format. Use the sections that are helpful for the
project you want to propose, and discuss the design itself in a GitHub issue before beginning a
large implementation.

# Project: topic
## 1. Goal
What is your goal? Why is it important?

## 2. Core Math
Which theorem (big or small) marks this roadmap as done?
What informal math (paper or textbook) are you formalizing?

## 3. Scope /Out of scope
What definitions and results will you formalize?
What related topics will you leave out, and why?

## 4. Design decisions and conventions
Fix some design choices (select items below that are applicable to your goal):
- Carrier type: what Lean type represents the object you study (e.g. a plain function, a structure, a measure)?
- Namespace: which namespace will your definitions and lemmas live in?
- Parameter order: in what order does each definition take its arguments, given that this fixes what can be partially applied?
- Totalization/boundary behavior: what do your functions return where the math is undefined (junk values such as `x / 0 = 0`)?
- Composition convention: if your objects compose, what does `f.comp g` mean and in which order does it apply?
- Typeclass assumptions: what minimal structure (e.g. `[MeasurableSpace Ω]`, `[Fintype ι]`) does each definition or theorem require?
- Finite/infinite conventions: do you assume finite or general settings (sums vs. integrals, `ℝ` vs. `ℝ≥0∞`/`EReal`)?

You might present the code in 
```lean
```

## 5. Proposed file organization and namespace

```text
Project/Area/Basic.lean
Project/Area/Operations.lean
Project/Area/MainTheorem.lean
``` 
