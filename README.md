# Type theory in SWI-Prolog

This project is meant to be an interactive tutorial on type theory, starting from the very basics. SWI-Prolog is used as an approximation of the natural deduction / sequent-calculus style systems that are typically used to formulate systems of type theory.

### Run the examples:
`> swipl -s STT/swipl_stt_tree_examples.pl`

`?- run.`

## FAQ
### Why do you need to encode the principle of explosion?

It lets you eliminate impossible cases. Take for example the proposition:

`forall x:Nat, (x > 1) -> (x \= x^2)`

You can prove propositions `forall x:Nat, P(x)` by case matching on `x:Nat`, i.e.:
`
proof : forall x:Nat, (x > 1) -> (x \= x^2)
proof 0 x_gt_1 = x_neq_x2
proof (S n) x_gt_1 = x_neq_x2
`

Only problem is that there's no way to fill in the RHS `x_neq_x2` for the 0 case, because in fact `0 = 0^2`. But `x=0` violates our other assumption that `x > 1`, i.e. `0 > 1` is false. So we can derive a contradiction a proof `f:False` from the assumption `0 > 1` and satisfy the RHS with `explosion(f)`.

Since there's no way to actually satisfy `0 > 1`, you can never actually call `proof` on that case (except under a hypothetical)
