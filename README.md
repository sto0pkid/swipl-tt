# Type theory in SWI-Prolog

This project is meant to be an interactive tutorial on type theory, starting from the very basics. SWI-Prolog is used as an approximation of the natural deduction / sequent-calculus style systems that are typically used to formulate systems of type theory.

## Tutorial

"Natural Deduction and the Curry-Howard Isomorphism", Andreas Abel: http://www.cse.chalmers.se/~abela/eafit2017/lecture1-nd.pdf
* Figure 1: Intuitionistic propositional logic, without explicit hypotheses
* Figure 2: Intuitionistic propositional logic, _with_ explicit hypotheses
	* corresponds to `IPL/swipl_ipl.pl`
* Page 16: Simply typed lambda calculus
	* corresponds to `STT/swipl_stt_judgements5.pl`
* Page 20: Curry-Howard isomorphism table
	* expresses direct correspondence between the rules of IPL with explicit hypotheses and simply typed lambda calculus.

"A Couple Of Meta-interpreters In Prolog", Markus Triska: https://www.metalevel.at/acomip/
* see section "Showing proofs" and compare with the IPL and STT formulations; see comments in `IPL/swipl_ipl.pl`



## FAQ
### Why do you need to encode the principle of explosion?

#### On a practical level
It lets you eliminate impossible cases. Take for example the proposition:

	forall x:Nat, (x > 1) -> (x \= x^2)

You can prove propositions `forall x:Nat, P(x)` by case matching on `x:Nat`, i.e.:

	proof : forall x:Nat, (x > 1) -> (x \= x^2)
	proof     0 x_gt_1 = x_neq_x2
	proof (S n) x_gt_1 = x_neq_x2

Only problem is that there's no way to fill in the RHS `x_neq_x2` for the 0 case, because in fact `0 = 0^2`. But `x=0` violates our other assumption that `x > 1`, i.e. `0 > 1` is false. So we can derive a contradiction, a proof `f:False` from the assumption `0 > 1` and satisfy the RHS with `explosion(f)`.

Since there's no way to actually satisfy `0 > 1`, you can never actually call `proof` on that case (except under a hypothetical), so you never run into a situation where you run a function and get `explosion(f)` as the output. The case is impossible, and all we've done is proved it in order to eliminate the case from consideration in our proof.

In some cases you can describe exactly the domain you want to your proof to cover so that there are no impossible cases to eliminate and therefore no need to use principle of explosion. For example:

	data NatsGreaterThan1 : Set
		2 : NatsGreaterThan1
		suc : NatsGreaterThan1 -> NatsGreaterThan1
	
	interpret : NatsGreaterThan1 -> Nat
	interpret 2 = suc(suc(0))
	interpret (suc(N)) = suc(interpret(N))

	proof : forall x:NatsGreaterThan1, interpret(x) \= interpret(x)^2
	proof	  2 = x_neq_x2
	proof (S n) = x_neq_x2

I don't know if there are limitations to this trick or if it's always at least theoretically possible but it's often the case that subsets are referenced in the former way, i.e. by quantifying over the base type (i.e. `Nat`) and using a proposition (i.e. `x > 1`) to specify the members of the subset, and this is the situation where principle of explosion is useful. An example where it might be harder to use this trick would be when the base type is `TuringMachine` and the proposition used to specify members of the subset is `halts(x)`.

#### On a theoretical level

The principle is "just kinda there", at least in this general framework of logic.

On a proof-theoretic level, the principle of explosion simply arises from the general principle for defining positive types from their introduction rules. If you look at the introduction rules for the empty type (there are none) and then define the (positive) elimination rule for it based on those rules, it's the principle of explosion. The general principle for defining positive types is what gives us rules for, ex.. enum/union types of any number of elements. If we take the enum/union type of 0 elements, it's the empty type and the elimination rule for it is the principle of explosion in the same pattern as how the elimination rule is defined for any other number of elements.

On a set-theoretic level, the principle of explosion is a consequence of the fact that the empty set is a subset of every set, so any inhabitant of the empty set must be an inhabitant of every set, which corresponds to any proof of the False type being a proof of every proposition (under the interpretation of propositions as the sets of their proofs).

### Why can't propositions inspect the internal behavior/properties of functions?
Because functions are *defined* not to have any "internal behavior/properties", and even in their implementation they don't really have any. Take for example the function 

	_+_ : nat -> nat -> nat
	0 	+ y = y
	(suc x) + y = suc (x + y)

We can apply this and get a result:

	2 + 2
	= (suc (suc 0)) + (suc (suc 0))
	= suc ((suc 0) + (suc (suc 0)))
	= suc (suc (0 + (suc (suc 0))))
	= suc (suc (suc (suc 0)))
	= 4

We could have alternatively defined `_+_` like:

	_+'_ : nat -> nat -> nat
	x +' 0 = x
	x +' (suc y) = suc (x + y)

And its application would look like

	2 +' 2
	= (suc (suc 0)) +' (suc (suc 0))
	= suc ((suc (suc 0)) +' (suc 0))
	= suc (suc ((suc (suc 0)) +' 0))
	= suc (suc (suc (suc 0)))
	= 4

These two definitions calculate the same outputs for the same inputs but they take different sequences of steps to get there. Is that not the "internal behavior/properties" we're looking for? In fact it's not! These are indeed different sequences of steps but they're happening *outside* the function. The terms `2 + 2` and `2 +' 2` are *already* the function outputs, and the sequences of steps are simply a reduction of that output to a normal form. There is no internal behavior, they are mathematical functions, just as we've defined them to be!

Ok but still, you could hypothetically associate this reduction behavior or some other "internal" property like the string representations of these functions. But there's a reason we wouldn't want to do that: if we're *defining* these objects to be mathematical functions, then by the definition of equality of functions, they are equal if they have equal outputs for equal inputs. And a defining property of equality is the principle of substitution: given a proposition `P`, if `P(x)` is true, and `x = y`, then `P(y)` is true.

	principle_of_substitution : x = y -> P(x) -> P(y)


But if `P` is a proposition about some "internal" property of functions, and we have two functions `f` and `g` with `f = g` but with `P(f)` true and `P(g)` false, then by the principle of substitution we can get that `P(g)` is true from `P(f)` and `f = g`, but then we have a contradiction because we already have that `P(g)` is false. To restate:

	f = g -> P(f) -> ~P(g) -> false

because

	f = g -> P(f) -> P(g)

This would be a problem if we could express a proposition like `is_named_f`, we would have:

	is_named_f(f) /\ ~is_named_f(g)

but,

	f = g -> is_named_f(f) -> is_named_f(g)

so we'd have a contradiction.

So that's the fundamental reason we can't make propositions that inspect these "internal"/"implementation detail" properties of objects: the principle of substitution forces that if two objects are declared equal, then no proposition can distinguish them by being true for one and false for the other without yielding a contradiction.

And it's reasonable to say that this is a feature and not a bug, this is just the logic working correctly. This isn't to say that one shouldn't design their languages or extend the logic in such a way that you can inspect these internal properties of objects, but however that's done it probably shouldn't break the basic properties of extensional equality of functions or the principle of substitution.

TODO: ok so maybe we accept that we don't want to break our object language by trying to make it inspect things that we've defined not to exist in it, but these objects in our object language still do have "implementation" detail we want to be able to inspect in the full programming environment that surrounds that object language, what are possible approaches to incorporating inspection in an appropriate way?

TLDR: "inspection as godelization"; although we can't start with a function and get its representation propositionally, we can get its representation _judgementally_ and from the representation we _can_ propositionally recover the function (up to term equivalence!).
