(* =========================================================== *)
(**
* Coq Proof for the determination of equivalent interaction terms w.r.t. a denotational semantics
Erwan Mahe - 2021

We use Coq to:
- formally encode an Interaction Language for modelling the behavior of distributed systems
- define a formal semantics in denotational style on this language
- define an equivalence relation on interaction terms
- prove that equivalent interaction terms as defined by this relation have the same semantics

This proof accompanies the manuscript of my thesis

The coq file itself is hosted on the following repository:
- #<a href="https://github.com/erwanM974/coq_hibou_label_equivalent_terms">https://github.com/erwanM974/coq_hibou_label_equivalent_terms</a># 

** Context

This formal semantics defines which are the behaviors that are specified by an interaction model 
(akin to Message Sequence Charts or UML Sequence Diagrams).
Those behaviors are described by traces which are sequences of atomic actions that can be observed 
on the interfaces of a distributed system's sub-systems.
Those atomic actions correspond to the occurence of communication events i.e. either the emission or the reception of
a given message on a given sub-system.

** Dependencies
Below are listed the libraries required for this Coq proof.
- "Coq.Lists.List." provides utilities on lists. I use lists - among other things - to represent traces.
- "Coq.Vectors.Fin." provides a means to represent finite sets indexed by {1,...,n}.
- "Psatz." is required for using the "lia" tactic to solve simple arithemtic problems.
- "Coq.Program.Equality." is required for using the "dependent induction" tactic with "generalizing", allowing the generalisation of some variables of the problem in the induction hypothesis.
- "Coq.Init.Logic." for (among other things) the "not_eq_sym" theorem
- "Coq.Init.Nat.", "Coq.Arith.PeanoNat." and "Coq.Arith.Peano_dec." for the manipulation of natural integers and the use of some lemmas
**)

Require Import Coq.Lists.List.
Require Coq.Vectors.Fin.
Require Import Psatz.
Require Import Coq.Program.Equality.
Require Import Coq.Init.Logic. 
Require Import Coq.Init.Nat.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Peano_dec.

(**
* Preliminaries

This section is dedicated to enoncing some basic types and properties on which the remainder of the proof will be based.

** Substitutions and eliminations of elements in lists

In the following, I define some functions to manipulate lists. 
To do so, I use Fixpoints and as a result those functions are checked by Coq's termination checker.

- "list_replace_nth" replaces the "n-th" element of a list by another element
- "list_remove_nth" removes the "n-th" element of a list
**)

Fixpoint list_replace_nth (A:Type) (n:nat) (l:list A) (x:A) {struct l} : list A :=
    match n, l with
      | O, e :: l' => x :: l'
      | O, other => nil
      | S m, nil => nil
      | S m, e :: l' => e :: (list_replace_nth A m l' x)
    end.

Fixpoint list_remove_nth (A:Type) (n:nat) (l:list A) {struct l} : list A :=
    match n, l with
      | O, e :: l' => l'
      | O, other => nil
      | S m, nil => nil
      | S m, e :: l' => e :: (list_remove_nth A m l')
    end.

(** 
** Signature & Actions

The interaction language that I define depends on a signature that is composed of:
- a set of "lifelines" L, which elements represent the individual sub-systems that can be found in the disctributed system (or some groups of sub-systems via abstraction/refinement)
- a set of "messages" M, which elements represent the individual distinguishable messages that can be exchanged (via asynchronous communication) within (i.e. internally) or without (i.e externally) the distributed system 

Given that I consider finitely many such lifelines and messages, I use finite vectors from "Coq.Vectors.Fin."
to model those sets.
**)

Parameter LCard : nat.
Parameter MCard : nat.

Definition L := Fin.t (S LCard).
Definition M := Fin.t (S MCard).

(**
To distinguish between emissions "a!m" and receptions "b?m" I encode the kind of action ({!,?}) with an inductive type "ActKind".
**)

Inductive ActKind : Set :=
  |ak_snd:ActKind
  |ak_rcv:ActKind.

(**
I can now define actions with the "Action" type via a cartesian product of types L, ActKind and M.

A utility function "lifeline" returns, for any action, the lifeline on which it occurs.
**)

Definition Action :Set:= L*ActKind*M.

Definition lifeline: Action -> L :=
  fun '(_ as l,_,_) => l.

(* =========================================================== *)
(**
* Trace Language (Semantic Domain)

This section is dedicated to the semantic domain of our interaction language i.e. the domain of definition of its semantics.
After defining this domain, I will study the properties of this domain,
notably how one can manipulate its elements through some operators and which are the properties of those operators.

As hinted at ealier, in this modelling framework:
- it is the expected behavior of distributed systems that is modelled
- this behavior is expressed in terms of accepted traces i.e. sequences of atomic actions that may be expressed

The semantic domain is therefore the universe of traces.

The "Trace" type is formally defined below as that of lists of actions ("Action" type).

Functions "list_replace_nth" and "subs_remove" that were defined above to replace and remove elements in generic lists
are aliased and specialised for use in lists of traces as "subs_replace" and "subs_remove"
**)

Definition Trace : Type := list Action.

Definition subs_replace (n:nat) (subs:list Trace) (t:Trace) : list Trace 
  := list_replace_nth Trace n subs t. 

Definition subs_remove (n:nat) (subs:list Trace) : list Trace 
  := list_remove_nth Trace n subs. 

(**
** Some consideration on the decidability of equalities

In the following I construct the decidability of the equality of traces in several steps:
- in "eq_or_not_eq_actkind" is proven the decidability of the equality for the "ActKind" type. It is immediate given the inductive nature of "ActKind"
- in "eq_or_not_eq_action" is proven the decidability of the equality for the "Action" type. It relies on that of its subtypes L, ActKind and M. We have proven the decidability property for ActKind juste before, and, for L and M, it is provided by the "eq_dec" Lemma from "Coq.Vectors.Fin.". 
- finally, in "eq_or_not_eq_trace" it is proven for the "Trace" type

This last proof relies on a custom induction principle defined and checked in the "double_trace_induction" Lemma.
**)

Lemma eq_or_not_eq_actkind (x y:ActKind) :
  (x = y) \/ (x <> y).
Proof.
induction x; induction y.
- left. reflexivity.
- right. intro. discriminate.
- right. intro. discriminate.
- left. reflexivity.
Qed.

Lemma eq_or_not_eq_action (x y:Action) :
  (x = y) \/ (x <> y).
Proof.
destruct x ; destruct y.
destruct p ; destruct p0.
pose proof (Fin.eq_dec m m0) as Hm.
pose proof (Fin.eq_dec l l0) as Hl.
pose proof (eq_or_not_eq_actkind a a0) as Ha.
destruct Hm ; destruct Hl ; destruct Ha.
- destruct e ; destruct e0 ; destruct H.
  left. reflexivity.
- right. intro. injection H0. intros. contradiction.
- right. intro. injection H0. intros. contradiction.
- right. intro. injection H0. intros. contradiction.
- right. intro. injection H0. intros. contradiction.
- right. intro. injection H0. intros. contradiction.
- right. intro. injection H0. intros. contradiction.
- right. intro. injection H0. intros. contradiction.
Qed.

Lemma double_trace_induction (P: Trace -> Trace -> Prop):
  (P nil nil)
  -> (forall t:Trace, (t<>nil) -> ((P t nil) /\ (P nil t)) ) 
  -> (forall (a1 a2:Action) (t1 t2:Trace), P t1 t2 -> P (a1::t1) (a2::t2) ) ->
    forall (t1 t2:Trace), P t1 t2.
Proof.
intros.
dependent induction t1.
- induction t2.
  + assumption.
  + specialize H0 with (t:=(a::t2)).
    apply H0. intro. discriminate.
- dependent induction t2.
  + specialize H0 with (t:=(a::t1)).
    apply H0. intro. discriminate.
  + apply H1. apply IHt1.
Qed.

Lemma eq_or_not_eq_trace (x y:Trace) :
  (x = y) \/ (x <> y).
Proof.
pose proof double_trace_induction.
specialize H with (P:= (fun x y:Trace => (x = y) \/ (x <> y))).
apply H.
- left. reflexivity. 
- intros. split. 
  + right. assumption.
  + right. apply not_eq_sym. assumption.
- intros. destruct H0.
  + destruct H0.
    pose proof (eq_or_not_eq_action a1 a2).
    destruct H0.
    * destruct H0. left. reflexivity.
    * right. intro. inversion H1. contradiction.
  + right. intro. inversion H1. contradiction.
Qed.



(**
** Some operators on traces and some of their algebraic properties

In the following let us focus on four operators on traces:
- the classical concatenation of lists "++" which is extended to traces:
 - for any two traces t1 and t2, there is a single traces t such that t = t1 ++ t2
 - this traces t is defined as the concatenation of t1 and t2 as a single contiguous list
- an interleaving operator on traces
 - for any two traces t1 and t2, there can exist may traces t such that (is_interleaving t1 t2 t)
 - those traces correspond to potential interleavings of the actions from t1 and t2
 - within such a t, one must find all the actions from t1 and all the actions from t2 in the order in which they are found in t1 and t2 respectively
 - however actions from t1 can be put in any order w.r.t. the actions from t2 
- a weak sequencing operator on traces:
 - for any two traces t1 and t2, there can exist may traces t such that (is_weak_seq t1 t2 t)
 - weak sequencing allows some interleaving between the actions from t1 and t2
 - however it is a more restrictive operator than interleaving given that it onlt allows some interleavings and not all
 - the definition of what is allowed or not is reliant upon a conflict operator
 - in a certain prefix of the trace t:
  - actions from t1 can be added freely
  - actions from t2 can only be added if they do not enter into conflict with the actions from t1 that are waiting to be added
 - the notion of conflict correspond to the fact, for two actions, to occur on the same lifeline 
- a special merge operator which merges an ordered list of traces into a single merged trace.
I define this operator in such a way that is is configurable so as to act
as any of three different merge operators:
 - the merging of traces using classical concatenation
 - the merging of traces using the interleaving operator
 - the merging of traces using the weak sequenceing operator

In this section, those four operators will be defined (except for the concatenation which is already provided by Coq)
and some of their properties stated and proven.
**)


(**
*** Interleaving

I formalise the interleaving operator in Coq using an inductive predicate 
"is_interleaving" such that
"(is_interleaving t1 t2 t)" states the membership of a given trace t
into the set of interleavings between traces t1 and t2.

This inductive predicate can be inferred inductively using four construction rules:
- "interleaving_nil_left" which states that for any trace t, t is an interleaving of the empty trace and t
- "interleaving_nil_right" which states that for any trace t, t is an interleaving of t and the empty trace
- "interleaving_cons_left" which states that for any interleaving t of traces t1 and t2, (a::t) is an interleaving of (a::t1) and t2
- "interleaving_cons_right" which states that for any interleaving t of traces t1 and t2, (a::t) is an interleaving of t1 and (a::t2)

Those two last rules signify that, when constructing an interleaving, we can mix in actions from either traces in any order
**)

Inductive is_interleaving : Trace -> Trace -> Trace -> Prop :=
| interleaving_nil_left   : forall (t:Trace), 
                              (is_interleaving nil t t)
| interleaving_nil_right  : forall (t:Trace), 
                              (is_interleaving t nil t)
| interleaving_cons_left  : forall (t t1 t2:Trace) (a:Action),
                              (is_interleaving t1 t2 t) -> (is_interleaving (a::t1) t2 (a::t))
| interleaving_cons_right : forall (t t1 t2:Trace) (a:Action),
                              (is_interleaving t1 t2 t) -> (is_interleaving t1 (a::t2) (a::t)).

(**
Interesting properties of the "is_interleaving" that will be useful later on include:
- the guarantee of the existence of an interleaving t (at least one) for any traces t1 and t2 "is_interleaving_existence"
- "is_interleaving_nil_prop1", which states that if the empty trace is an interleaving of t1 and t2, then both t1 and t2 must be empty
- "is_interleaving_nil_prop2", which states that if t is an interleaving of the empty trace and t2, then t=t2
- "is_interleaving_nil_prop3", which states that if t is an interleaving of t1 and the empty trace, then t=t1
- "is_interleaving_split", which states that if a trace of the form (a::t) is an interleaving of traces t1 and t2 then the head action "a" can be found in:
 - either t1, which implies the existence of trace t3 such that t1=a::t3 and (is_interleaving t3 t2 t)
 - or t2, which implies the existence of trace t3 such that t2=a::t3 and (is_interleaving t1 t3 t)
**)

Lemma is_interleaving_existence (t1 t2:Trace) :
  exists t:Trace, is_interleaving t1 t2 t.
Proof.
dependent induction t1.
- exists t2. apply interleaving_nil_left.
- specialize IHt1 with (t2:=t2).
  destruct IHt1.
  exists (a::x).
  apply interleaving_cons_left.
  assumption.
Qed.

Lemma is_interleaving_nil_prop1 (t1 t2: Trace) :
  (is_interleaving t1 t2 nil)
  -> ( (t1 = nil) /\ (t2 = nil) ).
Proof.
intros H.
inversion H ; split ; reflexivity.
Qed.

Lemma is_interleaving_nil_prop2 (t t2: Trace) :
  (is_interleaving nil t2 t)
  -> (t2 = t).
Proof.
intros H.
dependent induction H.
- reflexivity.
- reflexivity.
- assert (t2=t).
  { apply IHis_interleaving.
    trivial.
  }
  destruct H0.
  reflexivity.
Qed.

Lemma is_interleaving_nil_prop3 (t1 t: Trace) :
  (is_interleaving t1 nil t)
  -> (t1 = t).
Proof.
intros H.
dependent induction H.
- reflexivity.
- reflexivity.
- assert (t1=t).
  { apply IHis_interleaving.
    trivial.
  }
  destruct H0.
  reflexivity.
Qed.

Lemma is_interleaving_split (a:Action) (t1 t2 t:Trace) :
  (is_interleaving t1 t2 (a :: t))
  -> (
       (exists t3:Trace, (t2=a::t3)/\(is_interleaving t1 t3 t))
       \/ (exists t3:Trace, (t1=a::t3)/\(is_interleaving t3 t2 t))
     ).
Proof.
intros.
dependent induction H.
- left. exists t. split.
  + reflexivity.
  + apply interleaving_nil_left.
- right. exists t. split.
  + reflexivity.
  + apply interleaving_nil_right.
- right. exists t1. split.
  + reflexivity.
  + assumption.
- left. exists t2. split.
  + reflexivity.
  + assumption.
Qed. 

(**
Other interesting properties of the "is_interleaving" include:
- "is_interleaving_symmetry", which states that the operator is symmetric i.e. if t is an interleaving of t1 and t2 then it is also an interleaving of t2 and t1
- "is_interleaving_left_associativity", which states that if t is an interleaving of t1 and t2 and if t1 can be decomposed as an interleaving of t1A and t1B then t is an interleaving of t1A with a certain tm that is an interleaving of t1B and t2
- "is_interleaving_right_associativity", which states that if t is an interleaving of t1 and t2 and if t2 can be decomposed as an interleaving of t2A and t2B then t is an interleaving of a certain tm with t2B, with that certain tm an interleaving of t1 and t2A
**)

Lemma is_interleaving_symmetry (t1 t2 t:Trace) :
  (is_interleaving t1 t2 t) <-> (is_interleaving t2 t1 t).
Proof.
split ; intros.
- dependent induction t generalizing t1 t2.
  + apply is_interleaving_nil_prop1 in H.
    destruct H. symmetry in H. destruct H.
    symmetry in H0. destruct H0.
    apply interleaving_nil_left.
  + apply is_interleaving_split in H.
    destruct H.
    * destruct H as (t3,H).
      destruct H.
      symmetry in H. destruct H.
      apply interleaving_cons_left. 
      apply IHt in H0.
      assumption.
    * destruct H as (t3,H).
      destruct H.
      symmetry in H. destruct H.
      apply interleaving_cons_right.
      apply IHt in H0.
      assumption.
- dependent induction t generalizing t1 t2.
  + apply is_interleaving_nil_prop1 in H.
    destruct H. symmetry in H. destruct H.
    symmetry in H0. destruct H0.
    apply interleaving_nil_left.
  + apply is_interleaving_split in H.
    destruct H.
    * destruct H as (t3,H).
      destruct H.
      symmetry in H. destruct H.
      apply interleaving_cons_left. 
      apply IHt in H0.
      assumption.
    * destruct H as (t3,H).
      destruct H.
      symmetry in H. destruct H.
      apply interleaving_cons_right.
      apply IHt in H0.
      assumption.
Qed.

Lemma is_interleaving_left_associativity (t1 t1A t1B t2 t:Trace) :
  ( (is_interleaving t1A t1B t1) /\ (is_interleaving t1 t2 t) )
  -> (exists tm:Trace, (is_interleaving t1B t2 tm) /\ (is_interleaving t1A tm t) ).
Proof.
intros.
destruct H.
dependent induction t generalizing t1 t1A t1B t2.
- apply is_interleaving_nil_prop1 in H0.
  destruct H0.
  symmetry in H0. destruct H0.
  symmetry in H1. destruct H1.
  apply is_interleaving_nil_prop1 in H.
  destruct H.
  symmetry in H0. destruct H0.
  symmetry in H. destruct H.
  exists nil.
  split ; apply interleaving_nil_left.
- inversion H0.
  + destruct H1. 
    symmetry in H2. destruct H2.
    symmetry in H3. destruct H3.
    clear H0.
    apply is_interleaving_nil_prop1 in H.
    destruct H.
    symmetry in H0. destruct H0.
    symmetry in H. destruct H.
    exists (a::t).
    split ; apply interleaving_nil_left.
  + destruct H2.
    symmetry in H1. destruct H1.
    symmetry in H3. destruct H3.
    clear H0.
    exists t1B.
    split.
    * apply interleaving_nil_right.
    * assumption.
  + destruct H2.
    symmetry in H3. destruct H3.
    symmetry in H1. destruct H1.
    symmetry in H5. destruct H5.
    clear H0.
    inversion H.
    { destruct H0. destruct H1.
      symmetry in H2. destruct H2.
      clear H.
      exists (a::t).
      split.
      - apply interleaving_cons_left.
        assumption.
      - apply interleaving_nil_left.
    }
    { destruct H0. destruct H1.
      symmetry in H2. destruct H2.
      clear H.
      exists t2.
      split.
      - apply interleaving_nil_left.
      - apply interleaving_cons_left.
        assumption.
    }
    { destruct H1. 
      symmetry in H0. destruct H0.
      symmetry in H2. destruct H2.
      symmetry in H5. destruct H5.
      specialize IHt with (t1:=t3) (t1A:=t1) (t1B:=t1B) (t2:=t2).
      assert (exists tm : Trace, is_interleaving t1B t2 tm /\ is_interleaving t1 tm t).
      { apply IHt ; assumption. }
      destruct H0 as (tm,H0).
      destruct H0.
      exists tm.
      split.
      - assumption.
      - apply interleaving_cons_left.
        assumption.
    }
    { symmetry in H1. destruct H1.
      symmetry in H0. destruct H0.
      destruct H5. destruct H2.
      specialize IHt with (t1:=t0) (t1A:=t1A) (t1B:=t4) (t2:=t2).
      assert (exists tm : Trace, is_interleaving t4 t2 tm /\ is_interleaving t1A tm t).
      { apply IHt ; assumption. }
      destruct H0 as (tm,H0).
      destruct H0.
      exists (a::tm).
      split.
      - apply interleaving_cons_left. assumption.
      - apply interleaving_cons_right. assumption.
    }
  + destruct H3.
    symmetry in H1. destruct H1.    
    symmetry in H2. destruct H2.    
    symmetry in H5. destruct H5.
    clear H0.
    specialize IHt with (t1:=t1) (t1A:=t1A) (t1B:=t1B) (t2:=t4).
    assert (exists tm : Trace, is_interleaving t1B t4 tm /\ is_interleaving t1A tm t).
    { apply IHt ; assumption. }
    destruct H0 as (tm,H0).
    destruct H0.
    exists (a::tm).
    split.
    { apply interleaving_cons_right.
      assumption. }
    { apply interleaving_cons_right.
      assumption.
    }
Qed.

Lemma is_interleaving_right_associativity (t1 t2 t2A t2B t:Trace) :
  ( (is_interleaving t2A t2B t2) /\ (is_interleaving t1 t2 t) )
  -> (exists tm:Trace, (is_interleaving t1 t2A tm) /\ (is_interleaving tm t2B t) ).
Proof.
intros.
destruct H.
apply is_interleaving_symmetry in H0.
assert (exists tm : Trace, is_interleaving t2A t1 tm /\ is_interleaving t2B tm t).
{ apply (is_interleaving_left_associativity t2 t2B t2A t1 t).
  split.
  - apply is_interleaving_symmetry. assumption.
  - assumption.
}
destruct H1 as (tm,H1).
destruct H1.
exists tm.
split.
- apply is_interleaving_symmetry. assumption.
- apply is_interleaving_symmetry. assumption.
Qed.

(**
*** Weak Sequencing

As explained earlier, the weak sequencing operator on traces relies upon a notion of "conflict" between actions.
To encode it in code, I define the "no_conflict" inductive predicate such that (no_conflict t a) 
states that there are not actions in t that occur on the same lifeline as action "a".

This predicate can be inferred inductively from the following two rules:
- "no_conflict_nil", which states that for any action "a", there can be no conflict between "a" and the empty trace
- "no_conflict_cons", which states that for any action "a" and trace (a'::t) which starts with action "a'" as its head, if "a" and "a'" occur on different lifelines and there is no conflict between "a" and "t" then there is no conflict between "a" and (a'::t)
**)

Inductive no_conflict : Trace -> Action -> Prop :=
| no_conflict_nil  : forall (a:Action), (no_conflict nil a)
| no_conflict_cons : forall (a a':Action) (t:Trace),
                        (
                          (not ((lifeline a) = (lifeline a')))
                          /\ (no_conflict t a)
                        ) -> (no_conflict (a'::t) a).

(**
As for the interleaving, I formalise the weak sequencing operator in Coq using an inductive predicate 
"is_weak_seq" such that
"(is_weak_seq t1 t2 t)" states the membership of a given trace t
into the set of weakly sequenced traces between traces t1 and t2.

This inductive predicate can be inferred inductively using four construction rules:
- "weak_seq_nil_left" which states that for any trace t, t is a weak sequence of the empty trace and t
- "weak_seq_nil_right" which states that for any trace t, t is a weak sequence of t and the empty trace
- "weak_seq_cons_left" which states that for any weak sequence t of traces t1 and t2, (a::t) is a weak sequence of (a::t1) and t2
- "weak_seq_cons_right" which states that for any weak sequence t of traces t1 and t2, if there is no conflict between "a" and t1 then (a::t) is a weak sequence of t1 and (a::t2)

Those two last rules signify that, when constructing a weak sequence:
- we can freely add actions from the left-hand side trace t1
- but we only allow the addition of events from t2 if they are not preempted by the occurence of events from t1
**)

Inductive is_weak_seq : Trace -> Trace -> Trace -> Prop :=
| weak_seq_nil_left   : forall (t:Trace), 
                              (is_weak_seq nil t t)
| weak_seq_nil_right  : forall (t:Trace), 
                              (is_weak_seq t nil t)
| weak_seq_cons_left  : forall (t t1 t2:Trace) (a:Action),
                              (is_weak_seq t1 t2 t) -> (is_weak_seq (a::t1) t2 (a::t))
| weak_seq_cons_right : forall (t t1 t2:Trace) (a:Action),
                              (is_weak_seq t1 t2 t)
                              -> (no_conflict t1 a) 
                              -> (is_weak_seq t1 (a::t2) (a::t)).

(**
In a similar fashion to what I did for the interleaving operator, I state and prove in the following some properties on the weak sequencing operator:
- the guarantee of the existence of a weak sequence t (at least one) for any traces t1 and t2 "is_weak_seq_existence"
- "is_weak_seq_nil_prop1", which states that if the empty trace is a weak sequence of t1 and t2, then both t1 and t2 must be empty
- "is_weak_seq_nil_prop2", which states that if t is a weak sequence of the empty trace and t2, then t=t2
- "is_weak_seq_nil_prop3", which states that if t is a weak sequence of t1 and the empty trace, then t=t1
- "is_weak_seq_split", which states that if (a :: t) is a weak sequence of t1 and t2, then either t1 starts with "a" or t2 starts with "a" and there is no conflict between t1 and "a"
**)


Lemma is_weak_seq_existence (t1 t2:Trace) :
  exists t:Trace, is_weak_seq t1 t2 t.
Proof.
dependent induction t1.
- exists t2. apply weak_seq_nil_left.
- specialize IHt1 with (t2:=t2).
  destruct IHt1.
  exists (a::x).
  apply weak_seq_cons_left.
  assumption.
Qed.

Lemma is_weak_seq_nil_prop1 (t1 t2: Trace) :
  (is_weak_seq t1 t2 nil)
  -> ( (t1 = nil) /\ (t2 = nil) ).
Proof.
intros H.
inversion H ; split ; reflexivity.
Qed.

Lemma is_weak_seq_nil_prop2 (t1 t2: Trace) :
  (is_weak_seq nil t1 t2)
  -> (t1 = t2).
Proof.
intros H.
assert (H0:=H).
dependent induction H.
- reflexivity.
- reflexivity.
- assert (t2=t).
  { apply IHis_weak_seq.
    - trivial.
    - assumption.
  }
  destruct H2.
  reflexivity.
Qed.

Lemma is_weak_seq_nil_prop3 (t1 t2: Trace) :
  (is_weak_seq t1 nil t2)
  -> (t1 = t2).
Proof.
intros H.
dependent induction H.
- reflexivity.
- reflexivity.
- assert (t1=t).
  { apply IHis_weak_seq.
    trivial.
  }
  destruct H0.
  reflexivity.
Qed.

Lemma is_weak_seq_split (a:Action) (t1 t2 t:Trace) :
  (is_weak_seq t1 t2 (a :: t))
  -> (
       ( (no_conflict t1 a) /\ (exists t3:Trace, (t2=a::t3)/\(is_weak_seq t1 t3 t)) )
       \/ (exists t3:Trace, (t1=a::t3)/\(is_weak_seq t3 t2 t))
     ).
Proof.
intros.
dependent induction H.
- left. split.
  + apply no_conflict_nil.
  + exists t. split.
    * reflexivity.
    * apply weak_seq_nil_left.
- right. exists t. split.
  + reflexivity.
  + apply weak_seq_nil_right.
- right. exists t1. split.
  + reflexivity.
  + assumption.
- left. split.
  + assumption.
  + exists t2.
    split.
    * reflexivity.
    * assumption.
Qed.

(**
Before stating and proving some properties concerning a weak form of associativity for the weak sequencing operator, let us digress on the
relationships of the "no_conflict" function w.r.t. the operators.
In particular, we introduce the following Lemmas:
- "no_conflict_concat", which states that the fact that t1 and t2 both have no conflict w.r.t. an action a equates to the fact that their concatenation t1++t2 has no conflict w.r.t. action a 
- "no_conflict_interleaving", which is a similar lemma, but instead of considering the concatenation t1++t2, we consider any interleaving t of t1 and t2
- "no_conflict_weak_seq", which is also the same property, but instead of considering the concatenation t1++t2, we consider any weak sequence t of t1 and t2

In particular, the last Lemma "no_conflict_weak_seq" will be required to prove some further properties on the weak sequencing operator
given that its definition is tightly interlinked with that of no_conflict.
**)

Lemma no_conflict_concat (t1 t2:Trace) (a:Action) :
  ( (no_conflict t1 a) /\ (no_conflict t2 a) )
  <-> (no_conflict (t1++t2) a).
Proof.
split ; intros H.
- destruct H.
  dependent induction t1.
  + simpl. assumption.
  + simpl. apply no_conflict_cons.
    inversion H.
    destruct H4.
    split.
    * assumption.
    * apply IHt1.
      { assumption. }
      { assumption. }
- dependent induction t1.
  + simpl in H.
    split.
    * apply no_conflict_nil.
    * assumption.
  + simpl in H.
    inversion H.
    destruct H3.
    apply IHt1 in H4.
    destruct H4.
    split.
    * apply no_conflict_cons.
      split.
      { assumption. }
      { assumption. }
    * assumption.
Qed.

Lemma no_conflict_interleaving (t1 t2 t :Trace) (a:Action) :
  (is_interleaving t1 t2 t)
  -> (
       ( (no_conflict t1 a) /\ (no_conflict t2 a) )
       <-> (no_conflict t a)
     ).
Proof.
split ; intros H1. 
- destruct H1.
  dependent induction H.
  + assumption.
  + assumption.
  + apply no_conflict_cons.
    inversion H0. destruct H5.
    split.
    * assumption.
    * apply IHis_interleaving ; assumption.
  + apply no_conflict_cons.
    inversion H1. destruct H5.
    split.
    * assumption.
    * apply IHis_interleaving ; assumption.
- dependent induction H.
  + split.
    * apply no_conflict_nil.
    * assumption.
  + split.
    * assumption.
    * apply no_conflict_nil.
  + inversion H1.
    destruct H4. 
    apply IHis_interleaving in H5.
    destruct H5.
    split.
    * apply no_conflict_cons.
      split ; assumption.
    * assumption.
  + inversion H1.
    destruct H4. 
    apply IHis_interleaving in H5.
    destruct H5.
    split.
    * assumption.
    * apply no_conflict_cons.
      split ; assumption.
Qed.

Lemma no_conflict_weak_seq (t1 t2 t :Trace) (a:Action) :
  (is_weak_seq t1 t2 t)
  -> (
       ( (no_conflict t1 a) /\ (no_conflict t2 a) )
       <-> (no_conflict t a)
     ).
Proof.
split ; intros H1.
- destruct H1.
  dependent induction H.
  + assumption.
  + assumption.
  + apply no_conflict_cons.
    inversion H0. destruct H5.
    split.
    * assumption.
    * apply IHis_weak_seq ; assumption.
  + apply no_conflict_cons.
    inversion H2. destruct H6.
    split.
    * assumption.
    * apply IHis_weak_seq ; assumption.
- dependent induction H.
  + split.
    * apply no_conflict_nil.
    * assumption.
  + split.
    * assumption.
    * apply no_conflict_nil.
  + inversion H1.
    destruct H4. 
    apply IHis_weak_seq in H5.
    destruct H5.
    split.
    * apply no_conflict_cons.
      split ; assumption.
    * assumption.
  + inversion H1.
    destruct H5. 
    apply IHis_weak_seq in H6.
    destruct H6.
    split.
    * assumption.
    * apply no_conflict_cons.
      split ; assumption.
Qed.

(**
Like what we did for the interleaving operator, let us now study some properties of associativity for the weak sequencing operator.
The Lemmas:
- "is_weak_seq_left_associativity" states that if t is a weak sequence of t1 and t2 and if t1 can be decomposed as a weak sequence of t1A and t1B then t is a weak sequence of t1A with a certain tm that is a weak sequence of t1B and t2. Let us remark that we need the additional Lemma "no_conflict_weak_seq" for this proof.
- "is_weak_seq_right_associativity" states that if t is a weak sequence of t1 and t2 and if t2 can be decomposed as a weak sequence of t2A and t2B then t is a weak sequence of a certain tm with t2B, with that certain tm a weak sequence of t1 and t2A. We also need "no_conflict_weak_seq" here.
**)

Lemma is_weak_seq_left_associativity (t1 t1A t1B t2 t:Trace) :
  ( (is_weak_seq t1A t1B t1) /\ (is_weak_seq t1 t2 t) )
  -> (exists tm:Trace, (is_weak_seq t1B t2 tm) /\ (is_weak_seq t1A tm t) ).
Proof.
intros.
destruct H.
dependent induction t generalizing t1 t1A t1B t2.
- apply is_weak_seq_nil_prop1 in H0.
  destruct H0.
  symmetry in H0. destruct H0.
  symmetry in H1. destruct H1.
  apply is_weak_seq_nil_prop1 in H.
  destruct H.
  symmetry in H0. destruct H0.
  symmetry in H. destruct H.
  exists nil.
  split ; apply weak_seq_nil_left.
- inversion H0.
  + destruct H1. 
    symmetry in H2. destruct H2.
    symmetry in H3. destruct H3.
    clear H0.
    apply is_weak_seq_nil_prop1 in H.
    destruct H.
    symmetry in H0. destruct H0.
    symmetry in H. destruct H.
    exists (a::t).
    split ; apply weak_seq_nil_left.
  + destruct H2.
    symmetry in H1. destruct H1.
    symmetry in H3. destruct H3.
    clear H0.
    exists t1B.
    split.
    * apply weak_seq_nil_right.
    * assumption.
  + destruct H2.
    symmetry in H3. destruct H3.
    symmetry in H1. destruct H1.
    symmetry in H5. destruct H5.
    clear H0.
    inversion H.
    { destruct H0. destruct H1.
      symmetry in H2. destruct H2.
      clear H.
      exists (a::t).
      split.
      - apply weak_seq_cons_left.
        assumption.
      - apply weak_seq_nil_left.
    }
    { destruct H0. destruct H1.
      symmetry in H2. destruct H2.
      clear H.
      exists t2.
      split.
      - apply weak_seq_nil_left.
      - apply weak_seq_cons_left.
        assumption.
    }
    { destruct H1. 
      symmetry in H0. destruct H0.
      symmetry in H2. destruct H2.
      symmetry in H5. destruct H5.
      specialize IHt with (t1:=t3) (t1A:=t1) (t1B:=t1B) (t2:=t2).
      assert (exists tm : Trace, is_weak_seq t1B t2 tm /\ is_weak_seq t1 tm t).
      { apply IHt ; assumption. }
      destruct H0 as (tm,H0).
      destruct H0.
      exists tm.
      split.
      - assumption.
      - apply weak_seq_cons_left.
        assumption.
    }
    { destruct H1.
      symmetry in H0. destruct H0.
      destruct H3. destruct H2.
      specialize IHt with (t1:=t0) (t1A:=t1) (t1B:=t4) (t2:=t2).
      assert (exists tm : Trace, is_weak_seq t4 t2 tm /\ is_weak_seq t1 tm t).
      { apply IHt ; assumption. }
      destruct H0 as (tm,H0).
      destruct H0.
      exists (a::tm).
      split.
      - apply weak_seq_cons_left. assumption.
      - apply weak_seq_cons_right.
        + assumption.
        + assumption.
    }
  + destruct H4. 
    symmetry in H1. destruct H1.    
    symmetry in H2. destruct H2.    
    symmetry in H3. destruct H3.
    clear H0.
    specialize IHt with (t1:=t1) (t1A:=t1A) (t1B:=t1B) (t2:=t4).
    assert (exists tm : Trace, is_weak_seq t1B t4 tm /\ is_weak_seq t1A tm t).
    { apply IHt ; assumption. }
    destruct H0 as (tm,H0).
    destruct H0.
    exists (a::tm).
    apply (no_conflict_weak_seq t1A t1B t1 a) in H.
    apply H in H6. destruct H6. 
    split.
    { apply weak_seq_cons_right ; assumption. }
    { apply weak_seq_cons_right ; assumption. }
Qed.


Lemma is_weak_seq_right_associativity (t1 t2 t2A t2B t:Trace) :
  ( (is_weak_seq t2A t2B t2) /\ (is_weak_seq t1 t2 t) )
  -> (exists tm:Trace, (is_weak_seq t1 t2A tm) /\ (is_weak_seq tm t2B t) ).
Proof.
intros.
destruct H.
dependent induction t generalizing t1 t2 t2A t2B.
- apply is_weak_seq_nil_prop1 in H0.
  destruct H0.
  symmetry in H0. destruct H0.
  symmetry in H1. destruct H1.
  apply is_weak_seq_nil_prop1 in H.
  destruct H.
  symmetry in H0. destruct H0.
  symmetry in H. destruct H.
  exists nil.
  split ; apply weak_seq_nil_left.
- inversion H0.
  + exists t2A.
    split.
    * apply weak_seq_nil_left.
    * rewrite <- H3. assumption.
  + destruct H2.
    apply is_weak_seq_nil_prop1 in H.
    destruct H.
    symmetry in H. destruct H.
    symmetry in H2. destruct H2.
    exists (a::t).
    split ; apply weak_seq_nil_right.
  + destruct H2.
    symmetry in H1. destruct H1. 
    symmetry in H3. destruct H3. 
    symmetry in H5. destruct H5.
    assert (exists tm : Trace, is_weak_seq t3 t2A tm /\ is_weak_seq tm t2B t).
    { apply (IHt t3 t2 t2A t2B) ; assumption. }
    destruct H1 as (tm,H1). destruct H1.
    exists (a::tm).
    split.
    * apply weak_seq_cons_left. assumption.
    * apply weak_seq_cons_left. assumption.
  + destruct H4.
    symmetry in H1. destruct H1. 
    symmetry in H2. destruct H2.
    symmetry in H3. destruct H3.
    clear H0.
    inversion H.
    { destruct H0. destruct H1.
      symmetry in H2. destruct H2.
      clear H.
      exists t1.
      split.
      - apply weak_seq_nil_right.
      - apply weak_seq_cons_right ; assumption.
    }
    { destruct H0. destruct H1.
      symmetry in H2. destruct H2.
      clear H.
      exists (a::t).
      split.
      - apply weak_seq_cons_right ; assumption.
      - apply weak_seq_nil_right.
    }
    { destruct H1. 
      symmetry in H0. destruct H0.
      symmetry in H2. destruct H2.
      symmetry in H4. destruct H4.
      specialize IHt with (t1:=t1) (t2:=t4) (t2A:=t2) (t2B:=t2B).
      assert (exists tm : Trace, is_weak_seq t1 t2 tm /\ is_weak_seq tm t2B t).
      { apply IHt ; assumption. }
      destruct H0 as (tm,H0).
      destruct H0.
      exists (a::tm).
      split.
      - apply weak_seq_cons_right ; assumption.
      - apply weak_seq_cons_left.
        assumption.
    }
    { destruct H1.
      symmetry in H0. destruct H0.
      destruct H3. destruct H2.
      specialize IHt with (t1:=t1) (t2:=t0) (t2A:=t2) (t2B:=t3).
      assert (exists tm : Trace, is_weak_seq t1 t2 tm /\ is_weak_seq tm t3 t).
      { apply IHt ; assumption. }
      destruct H0 as (tm,H0).
      destruct H0.
      exists tm.
      split.
      - assumption.
      - apply weak_seq_cons_right.
        + assumption.
        + apply (no_conflict_weak_seq t1 t2 tm a).
          * assumption.
          * split ; assumption.
    }
Qed.

(**
*** Remark on the notion of scheduling & relative strength of scheduling operators

The three previously mentioned operators... 
- concatenation (also called strict sequencing)
- weak sequencing
- interleaving

... can be understood as scheduling operators i.e. they allow or disallow some reordering of
events from traces t1 and t2 in the construction of a merged trace t

I encode this notion of a type of scheduling into the inductive type "ScheduleKind" defined below.

**)

Inductive ScheduleKind : Set :=
  |lstrict:ScheduleKind
  |lseq:ScheduleKind
  |lpar:ScheduleKind.

(**
Let us remark, on the following Lemmas:
- "is_concat_implies_is_weak_seq" that any concatenation of two traces is a weak sequence of those traces
- "is_concat_implies_is_interleaving" that any concatenation of two traces is an interleaving of those traces
- "is_weak_seq_implies_is_interleaving" that any weak sequence of two traces is an interleaving of those traces
**)

Lemma is_concat_implies_is_weak_seq (t1 t2:Trace) :
  (is_weak_seq t1 t2 (t1 ++ t2)).
Proof.
dependent induction t1.
- simpl. apply weak_seq_nil_left.
- simpl. apply weak_seq_cons_left.
  apply IHt1.
Qed.

Lemma is_concat_implies_is_interleaving (t1 t2:Trace) :
  (is_interleaving t1 t2 (t1 ++ t2)).
Proof.
dependent induction t1.
- simpl. apply interleaving_nil_left.
- simpl. apply interleaving_cons_left.
  apply IHt1.
Qed.

Lemma is_weak_seq_implies_is_interleaving (t1 t2 t:Trace) :
  (is_weak_seq t1 t2 t)
  -> (is_interleaving t1 t2 t).
Proof.
intros.
dependent induction t generalizing t1 t2.
- apply is_weak_seq_nil_prop1 in H.
  destruct H.
  symmetry in H. destruct H.
  symmetry in H0. destruct H0.
  apply interleaving_nil_left.
- inversion H.
  + apply interleaving_nil_left.
  + apply interleaving_nil_right.
  + apply interleaving_cons_left.
    apply IHt. assumption.
  + apply interleaving_cons_right.
    apply IHt. assumption.
Qed.  

(**
As a result, we may conclude that the concatenation or strict sequencing operator is the most constraining while the interleaving operator is the least constraining.
We can therefore establish an order between those three scheduling operators, according to their strengths; this order being:
strict sequencing > weak sequencing > interleaving

This order is encoded into Coq with the "min_schedule_kind" function below, which for any two ScheduleKinds s1 and s2, returns the weakest.
**)

Definition min_schedule_kind (s1 s2:ScheduleKind) : ScheduleKind :=
  match s1 with
  | lpar => lpar
  | lseq => match s2 with
            | lpar => lpar
            | _ => lseq
            end
  | lstrict => s2
  end.

(**
*** Merge operator

The merge operator can be understood as a n-ary extension of the three previously defined scheduling operators.
For any list of traces [t1,t2,...,tn] and for any trace t_merge:
- saying that "t_merge is a merger of [t1,t2,...,tn] according to strict sequencing" signifies that t_merge is the concatenated trace t1++t2++...++tn
- saying that "t_merge is a merger of [t1,t2,...,tn] according to weak sequencing" signifies that t_merge verifies (is_weak_seq t1 t_remain t_merge) with t_remain being "a merger of [t2,...,tn] according to weak sequencing" and so on
- saying that "t_merge is a merger of [t1,t2,...,tn] according to interleaving" signifies that t_merge verifies (is_interleaving t1 t_remain t_merge) with t_remain being "a merger of [t2,...,tn] according to interleaving" and so on

I formalise the merge operator in Coq using an inductive predicate "n_merge_schedule"
such that for any schedule kind lk, for any list of non-empty traces "subs", and for any trace "t",
"(n_merge_schedule lk subs t)" states the membership of a given trace t into the set of mergers of traces from subs according to lk.

This inductive predicate can be inferred inductively using four construction rules:
- a construction rule "merge_zero" for the base case, which states that the empty trace is a merger of an empty list of traces
- and three construction rules, each dedicated to one of the three types of scheduling;
 - "merge_strict", which states that for any strict-merger t of traces from remain (a list of traces), then t1++t is a strict-merger of t1::remain
 - "merge_seq", which states that for any (weak) seq-merger t of traces from remain (a list of traces), then, for any trace t_merge verifying (is_weak_seq t1 t t_merge), we have that t_merge is a seq-merger of t1::remain
 - "merge_par", which states that for any par-merger t of traces from remain (a list of traces), then, for any trace t_merge verifying (is_interleaving t1 t t_merge), we have that t_merge is a par-merger of t1::remain
- let us note that for all three rules, we only allow the addition of non-empty traces in the list of traces to be merged. This is a modelisation choice.
**)
 
Inductive n_merge_schedule : 
  ScheduleKind -> list Trace -> Trace -> Prop :=
| merge_zero    : forall (lk:ScheduleKind),
                    (n_merge_schedule lk nil nil)
| merge_strict : forall (remain:list Trace) (t_first t_rep:Trace),
                    (t_first <> nil)
                    -> (n_merge_schedule lstrict remain t_rep)
                    -> (n_merge_schedule lstrict (t_first::remain) (t_first++t_rep))
| merge_seq    : forall (remain:list Trace) (t_first t_rep t_merge:Trace),
                    (t_first <> nil)
                    -> (n_merge_schedule lseq remain t_rep)
                    -> (is_weak_seq t_first t_rep t_merge)
                    -> (n_merge_schedule lseq (t_first::remain) t_merge)
| merge_par    : forall (remain:list Trace) (t_first t_rep t_merge:Trace),
                    (t_first <> nil)
                    -> (n_merge_schedule lpar remain t_rep)
                    -> (is_interleaving t_first t_rep t_merge)
                    -> (n_merge_schedule lpar (t_first::remain) t_merge).  

(**
In a similar fashion to what was done for the three scheduling operators, 
one can define an prove some properties for the merge operator:
- "no_conflict_n_merge" explains that is a merged trace t of a list of trace has no conflict with a certain action, then all the traces in that list have no conflict w.r.t. that action
- "n_merge_schedule_existence" guarantees the existence of a merged trace t (at least one) for any list of traces "subs" 
- "n_merge_schedule_nil_prop1" states that if the empty trace is a merger of a list of traces, then this list of traces is empty
- "n_merge_schedule_nil_prop2" states that if a trace is a merger of an empty list of traces, then it must be the empty trace
**)


Lemma no_conflict_n_merge (lk:ScheduleKind) (subs:list Trace) (t :Trace) (a:Action) :
  (n_merge_schedule lk subs t)
  -> (
       (no_conflict t a) 
       <-> (forall t0:Trace, (In t0 subs) -> (no_conflict t0 a))
     ).
Proof.
intros.
split ; intros.
- dependent induction subs.
  + contradiction.
  + inversion H.
    * destruct H2. destruct H3. destruct H4.
      destruct H6. simpl in *.
      apply (no_conflict_concat t_first t_rep a0) in H0.
      destruct H0.
      destruct H1.
      { destruct H1. assumption. }
      { apply (IHsubs t_rep) ; assumption. }
    * destruct H2. destruct H3. destruct H7.
      destruct H5. simpl in *.
      apply (no_conflict_weak_seq t_first t_rep) in H0.
      { destruct H0.
        destruct H1.
        - destruct H1. assumption.
        - apply (IHsubs t_rep) ; assumption.
      }
      { assumption. }
    * destruct H2. destruct H3. destruct H7.
      destruct H5. simpl in *.
      apply (no_conflict_interleaving t_first t_rep) in H0.
      { destruct H0.
        destruct H1.
        - destruct H1. assumption.
        - apply (IHsubs t_rep) ; assumption.
      }
      { assumption. }
- dependent induction subs.
  + inversion H. apply no_conflict_nil.
  + inversion H.
    * destruct H1. destruct H2. destruct H3.
      destruct H5.
      simpl in *.
      apply no_conflict_concat.
      split.
      { apply H0. left. reflexivity. }
      { apply IHsubs.
        - assumption.
        - intros t0 Ht0. 
          apply H0.
          right. assumption.
      }
    * destruct H1. destruct H2. destruct H4.
      destruct H6.
      simpl in *.
      apply (no_conflict_weak_seq t_first t_rep t_merge).
      { assumption. }
      { split.
        - apply H0. left. reflexivity.
        - apply IHsubs.
          + assumption.
          + intros t0 Ht0. 
            apply H0.
            right. assumption.
      }
    * destruct H1. destruct H2. destruct H4.
      destruct H6.
      simpl in *.
      apply (no_conflict_interleaving t_first t_rep t_merge).
      { assumption. }
      { split.
        - apply H0. left. reflexivity.
        - apply IHsubs.
          + assumption.
          + intros t0 Ht0. 
            apply H0.
            right. assumption.
      }
Qed.

Lemma n_merge_schedule_existence
  (lk:ScheduleKind) (subs:list Trace) :
   (forall t0:Trace, (In t0 subs) -> (t0<>nil) )
   -> (exists t:Trace, (n_merge_schedule lk subs t)).
Proof.
intros.
dependent induction subs.
- exists nil. apply merge_zero.
- destruct IHsubs.
  + intros. apply H. simpl. right. assumption.
  + destruct lk.
    { exists (a ++ x).
      apply merge_strict. 
      - apply H. simpl. left. reflexivity.
      - assumption.
    } 
    { pose proof (is_weak_seq_existence a x).
      destruct H1 as (t,H1). 
      exists t. 
      apply (merge_seq subs a x t).
      - apply H. simpl. left. reflexivity.
      - assumption.
      - assumption.
    }
    { pose proof (is_interleaving_existence a x).
      destruct H1 as (t,H1). 
      exists t. 
      apply (merge_par subs a x t).
      - apply H. simpl. left. reflexivity.
      - assumption.
      - assumption.
    }
Qed.

Lemma n_merge_schedule_nil_prop1 (lk:ScheduleKind) (subs:list Trace) :
  (n_merge_schedule lk subs nil)
  -> (subs=nil).
Proof.
intros.
inversion H.
- reflexivity.
- destruct H3. apply app_eq_nil in H0.
  destruct H0. symmetry in H3. destruct H3.
  rewrite app_nil_r in H1. contradiction.
- symmetry in H5. destruct H5. apply is_weak_seq_nil_prop1 in H2.
  destruct H2.
  symmetry in H2. destruct H2. contradiction.
- symmetry in H5. destruct H5. apply is_interleaving_nil_prop1 in H2.
  destruct H2.
  symmetry in H2. destruct H2. contradiction.
Qed.

Lemma n_merge_schedule_nil_prop2 (lk:ScheduleKind) (t_merge:Trace) :
  (n_merge_schedule lk nil t_merge)
  -> (t_merge=nil).
Proof.
intros.
dependent induction t_merge.
- reflexivity.
- inversion H.
Qed.



Lemma n_merge_strict_concat (sub1 sub2:list Trace) (t1 t2:Trace) :
  (n_merge_schedule lstrict sub1 t1)
  -> (n_merge_schedule lstrict sub2 t2)
  -> (n_merge_schedule lstrict (sub1 ++ sub2) (t1 ++ t2)).
Proof.
intros.
dependent induction H.
- simpl. assumption.
- rewrite <- (app_assoc t_first t_rep t2). apply merge_strict.
  + assumption.
  + apply IHn_merge_schedule.
    * reflexivity.
    * assumption.
Qed.

Lemma n_merge_schedule_weak_seq_split (subs:list Trace) (t:Trace) (a:Action) :
  (n_merge_schedule lseq subs (a :: t))
  -> (exists (n:nat) (tn : Trace), 
        (n<length subs)
        /\ (nth n subs nil = a :: tn)
        /\ (n_merge_schedule lseq (subs_replace n subs tn) t)
     ).
Proof.
Admitted.

Lemma n_merge_seq_replace_head_at_nth_on_first_sub (sub1 sub2:list Trace) (t tn:Trace) (a:Action) (n:nat) :
  ((nth n sub1 nil) = a::tn)
  ->
  (n_merge_schedule lseq ((subs_replace n sub1 tn)++sub2) t)
  ->
  (n_merge_schedule lseq (sub1 ++ sub2) (a :: t)).
Proof.
Admitted.

Lemma n_merge_seq_replace_head_at_nth_on_second_sub (sub1 sub2:list Trace) (t tn:Trace) (a:Action) (n:nat) :
  ((nth n sub2 nil) = a::tn)
  ->
  (n_merge_schedule lseq (sub1 ++ subs_replace n sub2 tn) t)
  ->
  (forall t1:Trace, In t1 sub1 -> no_conflict t1 a)
  -> 
  (n_merge_schedule lseq (sub1 ++ sub2) (a :: t)).
Proof.
Admitted.

Lemma n_merge_seq_weak_seq (sub1 sub2:list Trace) (t1 t2 t:Trace) :
  (n_merge_schedule lseq sub1 t1)
  -> (n_merge_schedule lseq sub2 t2)
  -> (is_weak_seq t1 t2 t)
  -> (n_merge_schedule lseq (sub1 ++ sub2) t).
Proof.
intros.
dependent induction t generalizing t1 t2 sub1 sub2.
- apply is_weak_seq_nil_prop1 in H1.
  destruct H1.
  symmetry in H1. destruct H1.
  symmetry in H2. destruct H2.
  apply n_merge_schedule_nil_prop1 in H.
  apply n_merge_schedule_nil_prop1 in H0.
  symmetry in H. destruct H.
  symmetry in H0. destruct H0.
  simpl. apply merge_zero.
- apply is_weak_seq_split in H1.
  destruct H1.
  + destruct H1. destruct H2 as (t3,H2).
    destruct H2.
    symmetry in H2. destruct H2.
    apply n_merge_schedule_weak_seq_split in H0.
    destruct H0 as (n,H0).
    destruct H0 as (tn,H0).
    destruct H0. destruct H2.
    assert (n_merge_schedule lseq (sub1 ++ (subs_replace n sub2 tn)) t).
    { apply (IHt t1 t3) ; assumption. }
    apply (n_merge_seq_replace_head_at_nth_on_second_sub sub1 sub2 t tn a n).
    * assumption.
    * assumption.
    * apply (no_conflict_n_merge lseq sub1 t1 a) in H.
      destruct H. apply H. assumption.
  + destruct H1 as (t3,H1).
    destruct H1.
    symmetry in H1. destruct H1.
    apply n_merge_schedule_weak_seq_split in H.
    destruct H as (n,H).
    destruct H as (tn,H).
    destruct H. destruct H1.
    assert (n_merge_schedule lseq ((subs_replace n sub1 tn) ++ sub2) t).
    { apply (IHt t3 t2) ; assumption. }
    apply (n_merge_seq_replace_head_at_nth_on_first_sub sub1 sub2 t tn a n).
    * assumption.
    * assumption.
Qed.

Lemma n_merge_schedule_interleaving_split (subs:list Trace) (t:Trace) (a:Action) :
  (n_merge_schedule lpar subs (a :: t))
  -> (exists (n:nat) (tn : Trace), 
        (n<length subs)
        /\ (nth n subs nil = a :: tn)
        /\ (n_merge_schedule lpar (subs_replace n subs tn) t)
     ).
Proof.
Admitted.

Lemma n_merge_par_replace_head_at_nth_on_first_sub (sub1 sub2:list Trace) (t tn:Trace) (a:Action) (n:nat) :
  ((nth n sub1 nil) = a::tn)
  ->
  (n_merge_schedule lpar ((subs_replace n sub1 tn)++sub2) t)
  ->
  (n_merge_schedule lpar (sub1 ++ sub2) (a :: t)).
Proof.
Admitted.

Lemma n_merge_par_replace_head_at_nth_on_second_sub (sub1 sub2:list Trace) (t tn:Trace) (a:Action) (n:nat) :
  ((nth n sub2 nil) = a::tn)
  ->
  (n_merge_schedule lpar (sub1 ++ subs_replace n sub2 tn) t)
  ->
  (n_merge_schedule lpar (sub1 ++ sub2) (a :: t)).
Proof.
Admitted.

Lemma n_merge_par_interleaving (sub1 sub2:list Trace) (t1 t2 t:Trace) :
  (n_merge_schedule lpar sub1 t1)
  -> (n_merge_schedule lpar sub2 t2)
  -> (is_interleaving t1 t2 t)
  -> (n_merge_schedule lpar (sub1 ++ sub2) t).
Proof.
intros.
dependent induction t generalizing t1 t2 sub1 sub2.
- apply is_interleaving_nil_prop1 in H1.
  destruct H1.
  symmetry in H1. destruct H1.
  symmetry in H2. destruct H2.
  apply n_merge_schedule_nil_prop1 in H.
  apply n_merge_schedule_nil_prop1 in H0.
  symmetry in H. destruct H.
  symmetry in H0. destruct H0.
  simpl. apply merge_zero.
- apply is_interleaving_split in H1.
  destruct H1.
  + destruct H1 as (t3,H1).
    destruct H1.
    symmetry in H1. destruct H1.
    apply n_merge_schedule_interleaving_split in H0.
    destruct H0 as (n,H0).
    destruct H0 as (tn,H0).
    destruct H0. destruct H1.
    assert (n_merge_schedule lpar (sub1 ++ (subs_replace n sub2 tn)) t).
    { apply (IHt t1 t3) ; assumption. }
    apply (n_merge_par_replace_head_at_nth_on_second_sub sub1 sub2 t tn a n).
    * assumption.
    * assumption.
  + destruct H1 as (t3,H1).
    destruct H1.
    symmetry in H1. destruct H1.
    apply n_merge_schedule_interleaving_split in H.
    destruct H as (n,H).
    destruct H as (tn,H).
    destruct H. destruct H1.
    assert (n_merge_schedule lpar ((subs_replace n sub1 tn) ++ sub2) t).
    { apply (IHt t3 t2) ; assumption. }
    apply (n_merge_par_replace_head_at_nth_on_first_sub sub1 sub2 t tn a n).
    * assumption.
    * assumption.
Qed.

Lemma n_merge_strict_implies_n_merge_seq (sub:list Trace) (t:Trace) :
  (n_merge_schedule lstrict sub t)
  -> (n_merge_schedule lseq sub t).
Proof.
intros.
dependent induction H.
- apply merge_zero.
- apply (merge_seq remain t_first t_rep (t_first++t_rep)).
  + assumption.
  + apply IHn_merge_schedule. reflexivity.
  + apply is_concat_implies_is_weak_seq.
Qed.

Lemma n_merge_seq_implies_n_merge_par (sub:list Trace) (t:Trace) :
  (n_merge_schedule lseq sub t)
  -> (n_merge_schedule lpar sub t).
Proof.
intros.
dependent induction H.
- apply merge_zero.
- apply (merge_par remain t_first t_rep t_merge).
  + assumption.
  + apply IHn_merge_schedule. reflexivity.
  + apply is_weak_seq_implies_is_interleaving.
    assumption.
Qed.

Lemma n_merge_strict_implies_n_merge_par (sub:list Trace) (t:Trace) :
  (n_merge_schedule lstrict sub t)
  -> (n_merge_schedule lpar sub t).
Proof.
intros.
apply n_merge_seq_implies_n_merge_par.
apply n_merge_strict_implies_n_merge_seq.
assumption.
Qed.







(**
* An Interaction Language and its semantics 

This section is dedicated to:
- the definition of the syntax of the interaction language. This syntax corresponds to the definition of a context-free grammar in which terms are build inductively from some basic terms and the application of some binary constructors to form more complex terms (as binary trees)
- the definition of a denotational-style semantics based on the composition of sets of traces using the previously defined operators on the semantic domain

** Syntax

We define the "Interaction" type, that inductively define interaction terms.
From basic building blocks which can either be the empty interaction "interaction_empty" or actions (of type "Action"), 
I then use different constructors to construct more complex interaction terms.

Let us describe the Coq definition, which includes 7 rules for the construction of the Interaction type:
- the "interaction_empty" constructor defines the empty interaction that can only express the empty trace nil
- the "interaction_act" cosntructor allows the construction of basic interactions that can only express a single trace (a::nil) for a given action "a"
- the "interaction_strict" constructor allows the construction of composed interactions of the form (interaction_strict i1 i2), where i1 and i2 are other (strictly smaller) interaction terms. (interaction_strict i1 i2) can express traces that are a strict sequencing of some trace expressed by i1 and some other expressed by i2
- likewise, (interaction_seq i1 i2) is an interaction that expresses traces that are weak sequences of traces expressed by i1 and i2
- also, (interaction_par i1 i2) is an interaction that expresses traces that are interleavings of traces expressed by i1 and i2
- the "interaction_alt" constructor allows the definition of interactions that can behave in a certain manner or (non-deterministically) in a certain other manner. Concretely, (interaction_alt i1 i2) expresses traces that are expressed either by i1 or by i2
- finally, the "interaction_loop" constructor allows the definition of interactions in which the behaviors of a given sub-interaction can be repeated an arbitraty number of times. This repetition is done according to one certain scheduling operator out of the three. Concretely:
 - a (interaction_loop lstrict i1) interaction expresses traces which are strict-mergers of traces that can be expressed by i1
 - a (interaction_loop lseq i1) interaction expresses traces which are seq-mergers of traces that can be expressed by i1
 - a (interaction_loop lpar i1) interaction expresses traces which are par-mergers of traces that can be expressed by i1
**)

Inductive Interaction : Set := 
  interaction_empty:Interaction 
  |interaction_act:Action->Interaction
  |interaction_strict:Interaction->Interaction->Interaction
  |interaction_seq:Interaction->Interaction->Interaction
  |interaction_par:Interaction->Interaction->Interaction
  |interaction_alt:Interaction->Interaction->Interaction
  |interaction_loop:ScheduleKind->Interaction->Interaction.


(**
** Denotational Semantics

Following the definition of the syntax, the informal description of the intended meaning of interaction terms,
and the previous preliminaries on the definition of operators for the semantic domain, we can immediately define the
denotational-style semantics as is done below.

We use a Fixpoint to define a function "sem_de" such that (sem_de i t) is a predicate which means that
the trace t can be expressed by the interaction i. 
In other words, this (sem_de i t) predicate states the membership of trace t into the semantics of interaction i.
**)
 
Fixpoint sem_de (i : Interaction) : (Trace -> Prop) :=
match i with
|interaction_empty          => fun t:Trace => 
                                  t = nil
|(interaction_act a)        => fun t:Trace => 
                                  t = a :: nil
|(interaction_alt i1 i2)    => fun t:Trace => 
                                  (sem_de i1 t) \/ (sem_de i2 t)
|(interaction_par i1 i2)    => fun t:Trace => 
                                  exists (t1 t2:Trace), 
                                    (sem_de i1 t1) /\ (sem_de i2 t2) /\ (is_interleaving t1 t2 t)
|(interaction_strict i1 i2) => fun t:Trace => 
                                  exists (t1 t2:Trace), 
                                    (sem_de i1 t1) /\ (sem_de i2 t2) /\ (t = t1 ++ t2)
|(interaction_seq i1 i2)    => fun t:Trace => 
                                  exists (t1 t2:Trace), 
                                    (sem_de i1 t1) /\ (sem_de i2 t2) /\ (is_weak_seq t1 t2 t)
|(interaction_loop lk i1)   => fun t:Trace => 
                                  exists (subs:list Trace),
                                    (forall (t0:Trace), (In t0 subs) -> (sem_de i1 t0) )
                                    /\ (n_merge_schedule lk subs t)
end.

(**
*** Some properties of "sem_de" w.r.t. loops

Let us remark the following:
- if an interaction "i" of the form "i = (interaction_loop lstrict i1)" accepts two traces t1 and t2:
 - then "i" must also accept t1++t2
- if an interaction "i" of the form "i = (interaction_loop lseq i1)" accepts two traces t1 and t2:
 - then "i" must also accept t1++t2
 - and, for any weak sequence t of t1 and t2, "i" must also accept t
- if an interaction "i" of the form "i = (interaction_loop lpar i1)" accepts two traces t1 and t2:
 - then "i" must also accept t1++t2
 - and, for any interleaving t of t1 and t2, "i" must also accept t

Those five properties are stated and proven in the five Lemmas below:
- "sem_de_loop_strict_concat_several"
- "sem_de_loop_seq_concat_several"
- "sem_de_loop_seq_weak_seq_several"
- "sem_de_loop_par_concat_several"
- "sem_de_loop_par_interleaving_several"
**)

Lemma sem_de_loop_strict_concat_several (i1:Interaction) (t1 t2:Trace) :
  (sem_de (interaction_loop lstrict i1) t1)
  -> (sem_de (interaction_loop lstrict i1) t2)
  -> (sem_de (interaction_loop lstrict i1) (t1 ++ t2)).
Proof.
intros.
simpl in *.
destruct H as (sub1,H1).
destruct H1 as (H1a,H1b).
destruct H0 as (sub2,H2).
destruct H2 as (H2a,H2b).
exists (sub1++sub2).
split.
- intros.
  apply in_app_or in H.
  destruct H.
  + apply H1a. assumption.
  + apply H2a. assumption.
- apply n_merge_strict_concat ; assumption.
Qed.

Lemma sem_de_loop_seq_concat_several (i1:Interaction) (t1 t2:Trace) :
  (sem_de (interaction_loop lseq i1) t1)
  -> (sem_de (interaction_loop lseq i1) t2)
  -> (sem_de (interaction_loop lseq i1) (t1 ++ t2)).
Proof.
intros.
simpl in *.
destruct H as (sub1,H1).
destruct H1 as (H1a,H1b).
destruct H0 as (sub2,H2).
destruct H2 as (H2a,H2b).
exists (sub1++sub2).
split.
- intros.
  apply in_app_or in H.
  destruct H.
  + apply H1a. assumption.
  + apply H2a. assumption.
- apply (n_merge_seq_weak_seq sub1 sub2 t1 t2 (t1++t2)).
  + assumption.
  + assumption.
  + apply (is_concat_implies_is_weak_seq t1 t2).
Qed.

Lemma sem_de_loop_seq_weak_seq_several (i1:Interaction) (t1 t2 t:Trace) :
  (sem_de (interaction_loop lseq i1) t1)
  -> (sem_de (interaction_loop lseq i1) t2)
  -> (is_weak_seq t1 t2 t)
  -> (sem_de (interaction_loop lseq i1) t).
Proof.
intros.
simpl in *.
destruct H as (subA,HA).
destruct HA as (HA1,HA2).
destruct H0 as (subB,HB).
destruct HB as (HB1,HB2).
exists (subA++subB).
split.
- intros.
  apply in_app_or in H.
  destruct H.
  + apply HA1. assumption.
  + apply HB1. assumption.
- apply (n_merge_seq_weak_seq subA subB t1 t2 t) ; assumption.
Qed.

Lemma sem_de_loop_par_concat_several (i1:Interaction) (t1 t2:Trace) :
  (sem_de (interaction_loop lpar i1) t1)
  -> (sem_de (interaction_loop lpar i1) t2)
  -> (sem_de (interaction_loop lpar i1) (t1 ++ t2)).
Proof.
intros.
simpl in *.
destruct H as (sub1,H1).
destruct H1 as (H1a,H1b).
destruct H0 as (sub2,H2).
destruct H2 as (H2a,H2b).
exists (sub1++sub2).
split.
- intros.
  apply in_app_or in H.
  destruct H.
  + apply H1a. assumption.
  + apply H2a. assumption.
- apply (n_merge_par_interleaving sub1 sub2 t1 t2 (t1++t2)).
  + assumption.
  + assumption.
  + apply (is_concat_implies_is_interleaving t1 t2).
Qed.


Lemma sem_de_loop_par_interleaving_several (i1:Interaction) (t1 t2 t:Trace) :
  (sem_de (interaction_loop lpar i1) t1)
  -> (sem_de (interaction_loop lpar i1) t2)
  -> (is_interleaving t1 t2 t)
  -> (sem_de (interaction_loop lpar i1) t).
Proof.
intros.
simpl in *.
destruct H as (subA,HA).
destruct HA as (HA1,HA2).
destruct H0 as (subB,HB).
destruct HB as (HB1,HB2).
exists (subA++subB).
split.
- intros.
  apply in_app_or in H.
  destruct H.
  + apply HA1. assumption.
  + apply HB1. assumption.
- apply (n_merge_par_interleaving subA subB t1 t2 t) ; assumption.
Qed.

(**
*** The inclusion of semantics for nested loops

In the following we will be interested in the question of the semantics of directly-nested loops i.e. interactions
of the form "i=loop_s1(loop_s2(i1))" where s1 and s2 are two ScheduleKinds.

We state and prove the following nine Lemmas:
- "sem_de_loop_max_schedule_inclusion_1", which states that the semantics of a "loop_strict(loop_strict(i1))" is exactly that of "loop_strict(i1)"
- "sem_de_loop_max_schedule_inclusion_2", which states that the semantics of a "loop_strict(loop_seq(i1))" is exactly that of "loop_seq(i1)"
- "sem_de_loop_max_schedule_inclusion_3", which states that the semantics of a "loop_strict(loop_par(i1))" is exactly that of "loop_par(i1)"
- "sem_de_loop_max_schedule_inclusion_4", which states that the semantics of a "loop_seq(loop_strict(i1))" is exactly that of "loop_seq(i1)"
- "sem_de_loop_max_schedule_inclusion_5", which states that the semantics of a "loop_seq(loop_seq(i1))" is exactly that of "loop_seq(i1)"
- "sem_de_loop_max_schedule_inclusion_6", which states that the semantics of a "loop_seq(loop_par(i1))" is exactly that of "loop_par(i1)"
- "sem_de_loop_max_schedule_inclusion_7", which states that the semantics of a "loop_par(loop_strict(i1))" is exactly that of "loop_par(i1)"
- "sem_de_loop_max_schedule_inclusion_8", which states that the semantics of a "loop_par(loop_seq(i1))" is exactly that of "loop_par(i1)"
- "sem_de_loop_max_schedule_inclusion_9", which states that the semantics of a "loop_par(loop_par(i1))" is exactly that of "loop_par(i1)"
**)

Lemma sem_de_loop_max_schedule_inclusion_1
  (i:Interaction) (t:Trace) :
  (sem_de (interaction_loop lstrict (interaction_loop lstrict i)) t)
  <-> (sem_de (interaction_loop lstrict i) t).
Proof.
split ; intros.
{
simpl in *.
destruct H as (sub0,H).
destruct H.
dependent induction sub0 generalizing t i.
- apply n_merge_schedule_nil_prop2 in H0.
  symmetry in H0. destruct H0.
  simpl. exists nil.
  split.
  + intros. contradiction.
  + apply merge_zero.
- inversion H0.
  destruct H1. destruct H2. destruct H5.
    assert (sem_de (interaction_loop lstrict i) t_first).
    { assert (In t_first (t_first::remain)). 
      { simpl. left. reflexivity. } 
      apply H in H1.
      destruct H1 as (sub1,H1). destruct H1.
      simpl. exists sub1.
      split.
      - intros. apply H1. assumption.
      - assumption.
    }
    assert (sem_de (interaction_loop lstrict i) t_rep).
    { simpl. apply IHsub0.
      - intros. apply H. simpl. right. assumption.
      - assumption.
    }
    apply sem_de_loop_strict_concat_several ; assumption.
}
{
pose proof (eq_or_not_eq_trace t nil).
destruct H0.
{ symmetry in H0. destruct H0.
  simpl. exists nil.
  split.
  - intros. contradiction.
  - apply merge_zero.
}
{ simpl in H.
  destruct H as (subs,H).
  destruct H.
  simpl.
  exists (t::nil).
  split.
  - intros. simpl in H2. destruct H2.
    + destruct H2.
      exists subs.
      split.
      * intros. apply H. assumption.
      * assumption.
    + contradiction.
  - rewrite <- app_nil_r. apply (merge_strict nil t nil).
    + assumption.
    + apply merge_zero.
}
}
Qed.

Lemma sem_de_loop_max_schedule_inclusion_2
  (i:Interaction) (t:Trace) :
  (sem_de (interaction_loop lstrict (interaction_loop lseq i)) t)
  <-> (sem_de (interaction_loop lseq i) t).
Proof.
split ; intros.
{
destruct H as (sub0,H).
destruct H.
dependent induction sub0 generalizing t i.
- apply n_merge_schedule_nil_prop2 in H0.
  symmetry in H0. destruct H0.
  simpl. exists nil.
  split.
  + intros. contradiction.
  + apply merge_zero.
- inversion H0.
  destruct H1. destruct H2. destruct H5.
    assert (sem_de (interaction_loop lseq i) t_first).
    { assert (In t_first (t_first::remain)). 
      { simpl. left. reflexivity. } 
      apply H in H1.
      destruct H1 as (sub1,H1). destruct H1.
      simpl. exists sub1.
      split.
      - intros. apply H1. assumption.
      - assumption.
    }
    assert (sem_de (interaction_loop lseq i) t_rep).
    { simpl. apply IHsub0.
      - intros. apply H. simpl. right. assumption.
      - assumption.
    }
    apply sem_de_loop_seq_concat_several ; assumption.
}
{
pose proof (eq_or_not_eq_trace t nil).
destruct H0.
{ symmetry in H0. destruct H0.
  simpl. exists nil.
  split.
  - intros. contradiction.
  - apply merge_zero.
}
{ simpl in H.
  destruct H as (subs,H).
  destruct H.
  simpl.
  exists (t::nil).
  split.
  - intros. simpl in H2. destruct H2.
    + destruct H2.
      exists subs.
      split.
      * intros. apply H. assumption.
      * assumption.
    + contradiction.
  - rewrite <- app_nil_r. apply (merge_strict nil t nil).
    + assumption.
    + apply merge_zero.
}
}
Qed.

Lemma sem_de_loop_max_schedule_inclusion_3
  (i:Interaction) (t:Trace) :
  (sem_de (interaction_loop lstrict (interaction_loop lpar i)) t)
  <-> (sem_de (interaction_loop lpar i) t).
Proof.
split ; intros.
{
destruct H as (sub0,H).
destruct H.
dependent induction sub0 generalizing t i.
- apply n_merge_schedule_nil_prop2 in H0.
  symmetry in H0. destruct H0.
  simpl. exists nil.
  split.
  + intros. contradiction.
  + apply merge_zero.
- inversion H0.
  destruct H1. destruct H2. destruct H5.
    assert (sem_de (interaction_loop lpar i) t_first).
    { assert (In t_first (t_first::remain)). 
      { simpl. left. reflexivity. } 
      apply H in H1.
      destruct H1 as (sub1,H1). destruct H1.
      simpl. exists sub1.
      split.
      - intros. apply H1. assumption.
      - assumption.
    }
    assert (sem_de (interaction_loop lpar i) t_rep).
    { simpl. apply IHsub0.
      - intros. apply H. simpl. right. assumption.
      - assumption.
    }
    apply sem_de_loop_par_concat_several ; assumption.
}
{
pose proof (eq_or_not_eq_trace t nil).
destruct H0.
{ symmetry in H0. destruct H0.
  simpl. exists nil.
  split.
  - intros. contradiction.
  - apply merge_zero.
}
{ simpl in H.
  destruct H as (subs,H).
  destruct H.
  simpl.
  exists (t::nil).
  split.
  - intros. simpl in H2. destruct H2.
    + destruct H2.
      exists subs.
      split.
      * intros. apply H. assumption.
      * assumption.
    + contradiction.
  - rewrite <- app_nil_r. apply (merge_strict nil t nil).
    + assumption.
    + apply merge_zero.
}
}
Qed.

Lemma sem_de_loop_max_schedule_inclusion_4
  (i:Interaction) (t:Trace) :
  (sem_de (interaction_loop lseq (interaction_loop lstrict i)) t)
  <-> (sem_de (interaction_loop lseq i) t).
Proof.
split ; intros.
{
destruct H as (sub0,H).
destruct H.
dependent induction sub0 generalizing t i.
- apply n_merge_schedule_nil_prop2 in H0.
  symmetry in H0. destruct H0.
  simpl. exists nil.
  split.
  + intros. contradiction.
  + apply merge_zero.
- inversion H0.
  destruct H1. destruct H2. destruct H6.
  assert (sem_de (interaction_loop lstrict i) t_first).
  { assert (In t_first (t_first::remain)). 
    { simpl. left. reflexivity. } 
    apply H in H1.
    destruct H1 as (sub1,H1). destruct H1.
    simpl. exists sub1.
    split.
    - intros. apply H1. assumption.
    - assumption.
  }
  assert (sem_de (interaction_loop lseq i) t_rep).
  { simpl. apply IHsub0.
    - intros. apply H. simpl. right. assumption.
    - assumption.
  }
  apply (sem_de_loop_seq_weak_seq_several i t_first t_rep t_merge).
  + simpl in H1.
    destruct H1 as (sub1,H1).
    destruct H1. simpl.
    exists sub1.
    split.
    * intros. apply H1. assumption.
    * apply n_merge_strict_implies_n_merge_seq.
      assumption.
  + assumption.
  + assumption.
}
{
pose proof (eq_or_not_eq_trace t nil).
destruct H0.
{ symmetry in H0. destruct H0.
  simpl. exists nil.
  split.
  - intros. contradiction.
  - apply merge_zero.
}
{ simpl in H.
  destruct H as (subs,H).
  destruct H.
  simpl.
  exists subs.
  split.
  - intros.
    pose proof (eq_or_not_eq_trace t0 nil).
    destruct H3.
    { symmetry in H3. destruct H3. exists nil.
      split.
      - intros. contradiction.
      - apply merge_zero.
    }
    { exists (t0::nil).
      split.
      - intros. simpl in H4. destruct H4.
        + apply H. destruct H4. assumption.
        + contradiction.
      - rewrite <- app_nil_r. apply (merge_strict nil t0 nil).
        + assumption.
        + apply merge_zero.
    }
  - assumption.
}
}
Qed.

Lemma sem_de_loop_max_schedule_inclusion_5
  (i:Interaction) (t:Trace) :
  (sem_de (interaction_loop lseq (interaction_loop lseq i)) t)
  <-> (sem_de (interaction_loop lseq i) t).
Proof.
split ; intros.
{
destruct H as (sub0,H).
destruct H.
dependent induction sub0 generalizing t i.
- apply n_merge_schedule_nil_prop2 in H0.
  symmetry in H0. destruct H0.
  simpl. exists nil.
  split.
  + intros. contradiction.
  + apply merge_zero.
- inversion H0.
  destruct H1. destruct H2. destruct H6.
    assert (sem_de (interaction_loop lseq i) t_first).
    { assert (In t_first (t_first::remain)). 
      { simpl. left. reflexivity. } 
      apply H in H1.
      destruct H1 as (sub1,H1). destruct H1.
      simpl. exists sub1.
      split.
      - intros. apply H1. assumption.
      - assumption.
    }
    assert (sem_de (interaction_loop lseq i) t_rep).
    { simpl. apply IHsub0.
      - intros. apply H. simpl. right. assumption.
      - assumption.
    }
    apply (sem_de_loop_seq_weak_seq_several i t_first t_rep t_merge) ; assumption.
}
{
pose proof (eq_or_not_eq_trace t nil).
destruct H0.
{ symmetry in H0. destruct H0.
  simpl. exists nil.
  split.
  - intros. contradiction.
  - apply merge_zero.
}
{ simpl in H.
  destruct H as (subs,H).
  destruct H.
  simpl.
  exists (t::nil).
  split.
  - intros. simpl in H2. destruct H2.
    + destruct H2.
      exists subs.
      split.
      * intros. apply H. assumption.
      * assumption.
    + contradiction.
  - apply (merge_seq nil t nil).
    + assumption.
    + apply merge_zero.
    + apply weak_seq_nil_right.
}
}
Qed.

Lemma sem_de_loop_max_schedule_inclusion_6
  (i:Interaction) (t:Trace) :
  (sem_de (interaction_loop lseq (interaction_loop lpar i)) t)
  <-> (sem_de (interaction_loop lpar i) t).
Proof.
split ; intros.
{
destruct H as (sub0,H).
destruct H.
dependent induction sub0 generalizing t i.
- apply n_merge_schedule_nil_prop2 in H0.
  symmetry in H0. destruct H0.
  simpl. exists nil.
  split.
  + intros. contradiction.
  + apply merge_zero.
- inversion H0.
  destruct H1. destruct H2. destruct H6.
    assert (sem_de (interaction_loop lpar i) t_first).
    { assert (In t_first (t_first::remain)). 
      { simpl. left. reflexivity. } 
      apply H in H1.
      destruct H1 as (sub1,H1). destruct H1.
      simpl. exists sub1.
      split.
      - intros. apply H1. assumption.
      - assumption.
    }
    assert (sem_de (interaction_loop lpar i) t_rep).
    { simpl. apply IHsub0.
      - intros. apply H. simpl. right. assumption.
      - assumption.
    }
    apply (sem_de_loop_par_interleaving_several i t_first t_rep t_merge).
    + assumption.
    + assumption.
    + apply is_weak_seq_implies_is_interleaving.
      assumption.
}
{
pose proof (eq_or_not_eq_trace t nil).
destruct H0.
{ symmetry in H0. destruct H0.
  simpl. exists nil.
  split.
  - intros. contradiction.
  - apply merge_zero.
}
{ simpl in H.
  destruct H as (subs,H).
  destruct H.
  simpl.
  exists (t::nil).
  split.
  - intros. simpl in H2. destruct H2.
    + destruct H2.
      exists subs.
      split.
      * intros. apply H. assumption.
      * assumption.
    + contradiction.
  - apply (merge_seq nil t nil).
    + assumption.
    + apply merge_zero.
    + apply weak_seq_nil_right.
}
}
Qed.

Lemma sem_de_loop_max_schedule_inclusion_7
  (i:Interaction) (t:Trace) :
  (sem_de (interaction_loop lpar (interaction_loop lstrict i)) t)
  <-> (sem_de (interaction_loop lpar i) t).
Proof.
split ; intros.
{
destruct H as (sub0,H).
destruct H.
dependent induction sub0 generalizing t i.
- apply n_merge_schedule_nil_prop2 in H0.
  symmetry in H0. destruct H0.
  simpl. exists nil.
  split.
  + intros. contradiction.
  + apply merge_zero.
- inversion H0.
  destruct H1. destruct H2. destruct H6.
  assert (sem_de (interaction_loop lstrict i) t_first).
  { assert (In t_first (t_first::remain)). 
    { simpl. left. reflexivity. } 
    apply H in H1.
    destruct H1 as (sub1,H1). destruct H1.
    simpl. exists sub1.
    split.
    - intros. apply H1. assumption.
    - assumption.
  }
  assert (sem_de (interaction_loop lpar i) t_rep).
  { simpl. apply IHsub0.
    - intros. apply H. simpl. right. assumption.
    - assumption.
  }
  apply (sem_de_loop_par_interleaving_several i t_first t_rep t_merge).
  + simpl in H1.
    destruct H1 as (sub1,H1).
    destruct H1. simpl.
    exists sub1.
    split.
    * intros. apply H1. assumption.
    * apply n_merge_strict_implies_n_merge_par.
      assumption.
  + assumption.
  + assumption.
}
{
pose proof (eq_or_not_eq_trace t nil).
destruct H0.
{ symmetry in H0. destruct H0.
  simpl. exists nil.
  split.
  - intros. contradiction.
  - apply merge_zero.
}
{ simpl in H.
  destruct H as (subs,H).
  destruct H.
  simpl.
  exists subs.
  split.
  - intros.
    pose proof (eq_or_not_eq_trace t0 nil).
    destruct H3.
    { symmetry in H3. destruct H3. exists nil.
      split.
      - intros. contradiction.
      - apply merge_zero.
    }
    { exists (t0::nil).
      split.
      - intros. simpl in H4. destruct H4.
        + apply H. destruct H4. assumption.
        + contradiction.
      - rewrite <- app_nil_r. apply (merge_strict nil t0 nil).
        + assumption.
        + apply merge_zero.
    }
  - assumption.
}
}
Qed.

Lemma sem_de_loop_max_schedule_inclusion_8
  (i:Interaction) (t:Trace) :
  (sem_de (interaction_loop lpar (interaction_loop lseq i)) t)
  <-> (sem_de (interaction_loop lpar i) t).
Proof.
split ; intros.
{
destruct H as (sub0,H).
destruct H.
dependent induction sub0 generalizing t i.
- apply n_merge_schedule_nil_prop2 in H0.
  symmetry in H0. destruct H0.
  simpl. exists nil.
  split.
  + intros. contradiction.
  + apply merge_zero.
- inversion H0.
  destruct H1. destruct H2. destruct H6.
  assert (sem_de (interaction_loop lseq i) t_first).
  { assert (In t_first (t_first::remain)). 
    { simpl. left. reflexivity. } 
    apply H in H1.
    destruct H1 as (sub1,H1). destruct H1.
    simpl. exists sub1.
    split.
    - intros. apply H1. assumption.
    - assumption.
  }
  assert (sem_de (interaction_loop lpar i) t_rep).
  { simpl. apply IHsub0.
    - intros. apply H. simpl. right. assumption.
    - assumption.
  }
  apply (sem_de_loop_par_interleaving_several i t_first t_rep t_merge).
  + simpl in H1.
    destruct H1 as (sub1,H1).
    destruct H1. simpl.
    exists sub1.
    split.
    * intros. apply H1. assumption.
    * apply n_merge_seq_implies_n_merge_par.
      assumption.
  + assumption.
  + assumption.
}
{
pose proof (eq_or_not_eq_trace t nil).
destruct H0.
{ symmetry in H0. destruct H0.
  simpl. exists nil.
  split.
  - intros. contradiction.
  - apply merge_zero.
}
{ simpl in H.
  destruct H as (subs,H).
  destruct H.
  simpl.
  exists subs.
  split.
  - intros.
    pose proof (eq_or_not_eq_trace t0 nil).
    destruct H3.
    { symmetry in H3. destruct H3. exists nil.
      split.
      - intros. contradiction.
      - apply merge_zero.
    }
    { exists (t0::nil).
      split.
      - intros. simpl in H4. destruct H4.
        + apply H. destruct H4. assumption.
        + contradiction.
      - apply (merge_seq nil t0 nil).
        + assumption.
        + apply merge_zero.
        + apply weak_seq_nil_right.
    }
  - assumption.
}
}
Qed.

Lemma sem_de_loop_max_schedule_inclusion_9
  (i:Interaction) (t:Trace) :
  (sem_de (interaction_loop lpar (interaction_loop lpar i)) t)
  <-> (sem_de (interaction_loop lpar i) t).
Proof.
split ; intros.
{
destruct H as (sub0,H).
destruct H.
dependent induction sub0 generalizing t i.
- apply n_merge_schedule_nil_prop2 in H0.
  symmetry in H0. destruct H0.
  simpl. exists nil.
  split.
  + intros. contradiction.
  + apply merge_zero.
- inversion H0.
  destruct H1. destruct H2. destruct H6.
    assert (sem_de (interaction_loop lpar i) t_first).
    { assert (In t_first (t_first::remain)). 
      { simpl. left. reflexivity. } 
      apply H in H1.
      destruct H1 as (sub1,H1). destruct H1.
      simpl. exists sub1.
      split.
      - intros. apply H1. assumption.
      - assumption.
    }
    assert (sem_de (interaction_loop lpar i) t_rep).
    { simpl. apply IHsub0.
      - intros. apply H. simpl. right. assumption.
      - assumption.
    }
    apply (sem_de_loop_par_interleaving_several i t_first t_rep t_merge) ; assumption.
}
{
pose proof (eq_or_not_eq_trace t nil).
destruct H0.
{ symmetry in H0. destruct H0.
  simpl. exists nil.
  split.
  - intros. contradiction.
  - apply merge_zero.
}
{ simpl in H.
  destruct H as (subs,H).
  destruct H.
  simpl.
  exists (t::nil).
  split.
  - intros. simpl in H2. destruct H2.
    + destruct H2.
      exists subs.
      split.
      * intros. apply H. assumption.
      * assumption.
    + contradiction.
  - apply (merge_par nil t nil t).
    + assumption.
    + apply merge_zero.
    + apply interleaving_nil_right.
}
}
Qed.

(**
Following the nine previous Lemmas, we have immediately the proof that the semantics of an interaction of the form
"loop_s1(loop_s2(i))" is exactly that of "loop_s(i)" where s is the minimum (as per the order of ScheduleKinds) between s1 and s2.

This observation is stated and proven in Lemma "sem_de_loop_max_schedule_inclusion"
**)

Lemma sem_de_loop_max_schedule_inclusion
  (i:Interaction) (s1 s2:ScheduleKind) (t:Trace) :
  (sem_de (interaction_loop s1 (interaction_loop s2 i)) t)
  <-> (sem_de (interaction_loop (min_schedule_kind s1 s2) i) t).
Proof.
intros.
destruct s1 ; destruct s2.
- apply sem_de_loop_max_schedule_inclusion_1.
- apply sem_de_loop_max_schedule_inclusion_2.
- apply sem_de_loop_max_schedule_inclusion_3.
- apply sem_de_loop_max_schedule_inclusion_4.
- apply sem_de_loop_max_schedule_inclusion_5.
- apply sem_de_loop_max_schedule_inclusion_6.
- apply sem_de_loop_max_schedule_inclusion_7.
- apply sem_de_loop_max_schedule_inclusion_8.
- apply sem_de_loop_max_schedule_inclusion_9.
Qed.



(**
* Equivalence classes for interaction terms

Let us now address the issue of determining equivalent interaction terms.

** Atomic transformations on the root of interactions

Let us start by defining some directed transformations that can be applied to the root of interactions
(i.e. modifying them from the root constructor, and not affecting its innermost sub-interactions).
Those transformations, we can intuitively guess, preserve the semantics.

In "is_root_equivalent_directed", we define those transformations, which are:
- the identity, encoded in Coq with "rooteq_self"
- three transformations corresponding to the elimination of the empty interaction when it is on the left of a schedule constructor:
 - "rooteq_simpl_left_strict" allows the transformation of strict(empty,i) into i
 - "rooteq_simpl_left_seq" allows the transformation of seq(empty,i) into i
 - "rooteq_simpl_left_par" allows the transformation of par(empty,i) into i
- three transformations corresponding to the elimination of the empty interaction when it is on the right of a schedule constructor:
 - "rooteq_simpl_right_strict" allows the transformation of strict(i,empty) into i
 - "rooteq_simpl_right_seq" allows the transformation of seq(i,empty) into i
 - "rooteq_simpl_right_par" allows the transformation of par(i,empty) into i
- four transformations corresponding to the manner in which nested constructors can be encoded using binary constructors:
 - "rooteq_flush_strict" allows the transformation of strict(strict(i1,i2),i3) into strict(i1,strict(i2,i3))
 - "rooteq_flush_seq" allows the transformation of seq(seq(i1,i2),i3) into seq(i1,seq(i2,i3))
 - "rooteq_flush_par" allows the transformation of par(par(i1,i2),i3) into par(i1,par(i2,i3))
 - "rooteq_flush_alt" allows the transformation of alt(alt(i1,i2),i3) into alt(i1,alt(i2,i3))
- two transformations corresponding to the manner in which one can order two sub-interactions in an alternative or parallel constructor:
 - "rooteq_invert_alt" allows the transformation of alt(i1,i2) into alt(i2,i1)
 - "rooteq_invert_par" allows the transformation of par(i1,i2) into par(i2,i1)
- that the proposition of an alternative between two identical sub-interaction is equivalent to that sub-interaction:
 - "rooteq_duplicate_alt" allows the transformation of alt(i,i) into i
- three transformations corresponding to the fact that if an alternative occurs between two sub-interactions, and, if those sub-interactions both start (w.r.t. a certain scheduling constructor) with the same sub-sub-interaction, then this sub-sub-interaction can be factorized w.r.t. the alternative: 
 - "rooteq_factorize_strict" allows the transformation of alt(strict(i1,i2),strict(i1,i3)) into strict(i1,alt(i2,i3))
 - "rooteq_factorize_seq" allows the transformation of alt(seq(i1,i2),seq(i1,i3)) into seq(i1,alt(i2,i3))
 - "rooteq_factorize_par" allows the transformation of alt(par(i1,i2),par(i1,i3)) into par(i1,alt(i2,i3))
- two transformations concern the transformation of interactions which root is a loop constructor
 - "rooteq_loop_simpl" allows the tranformation of interactions of the form loop_s(empty) into empty (for any ScheduleKind s)
 - "rooteq_loop_unnest" allows the transformation of interactions of the form loop_s1(loop_s2(i)) into loop_sm(i) where s1 and s2 are ScheduleKind and sm is the minimum (weakest) between s1 and s2
**)


Inductive is_root_equivalent_directed : Interaction -> Interaction -> Prop :=
| rooteq_self : forall (i:Interaction),
                       (is_root_equivalent_directed i i)
(* ================================================================================== *)
| rooteq_simpl_left_strict : forall (i:Interaction),
                       (is_root_equivalent_directed 
                           (interaction_strict interaction_empty i) 
                           i
                       )
| rooteq_simpl_left_seq : forall (i:Interaction),
                       (is_root_equivalent_directed 
                           (interaction_seq interaction_empty i) 
                           i
                       )
| rooteq_simpl_left_par : forall (i:Interaction),
                       (is_root_equivalent_directed 
                           (interaction_par interaction_empty i) 
                           i
                       )
(* ================================================================================== *)
| rooteq_simpl_right_strict : forall (i:Interaction),
                       (is_root_equivalent_directed 
                           (interaction_strict i interaction_empty)
                           i
                       )
| rooteq_simpl_right_seq : forall (i:Interaction),
                       (is_root_equivalent_directed 
                           (interaction_seq i interaction_empty) 
                           i
                       )
| rooteq_simpl_right_par : forall (i:Interaction),
                       (is_root_equivalent_directed 
                           (interaction_par i interaction_empty)
                           i
                       )
(* ================================================================================== *)
| rooteq_flush_strict : forall (i1 i2 i3:Interaction),
                       (is_root_equivalent_directed
                           (interaction_strict (interaction_strict i1 i2) i3) 
                           (interaction_strict i1 (interaction_strict i2 i3))
                       )
| rooteq_flush_seq    : forall (i1 i2 i3:Interaction),
                       (is_root_equivalent_directed
                           (interaction_seq (interaction_seq i1 i2) i3) 
                           (interaction_seq i1 (interaction_seq i2 i3))
                       )
| rooteq_flush_par    : forall (i1 i2 i3:Interaction),
                       (is_root_equivalent_directed
                           (interaction_par (interaction_par i1 i2) i3) 
                           (interaction_par i1 (interaction_par i2 i3))
                       )
| rooteq_flush_alt    : forall (i1 i2 i3:Interaction),
                       (is_root_equivalent_directed
                           (interaction_alt (interaction_alt i1 i2) i3) 
                           (interaction_alt i1 (interaction_alt i2 i3))
                       )
(* ================================================================================== *)
| rooteq_invert_alt    : forall (i1 i2:Interaction),
                       (is_root_equivalent_directed
                           (interaction_alt i1 i2) 
                           (interaction_alt i2 i1)
                       )
| rooteq_invert_par    : forall (i1 i2:Interaction),
                       (is_root_equivalent_directed
                           (interaction_par i1 i2) 
                           (interaction_par i2 i1)
                       )
(* ================================================================================== *)
| rooteq_duplicate_alt    : forall (i:Interaction),
                       (is_root_equivalent_directed
                           (interaction_alt i i)
                           i
                       )
(* ================================================================================== *)
| rooteq_factorize_strict : forall (i1 i2 i3:Interaction),
                       (is_root_equivalent_directed
                           (interaction_alt (interaction_strict i1 i2) (interaction_strict i1 i3)) 
                           (interaction_strict i1 (interaction_alt i2 i3))
                       )
| rooteq_factorize_seq : forall (i1 i2 i3:Interaction),
                       (is_root_equivalent_directed
                           (interaction_alt (interaction_seq i1 i2) (interaction_seq i1 i3)) 
                           (interaction_seq i1 (interaction_alt i2 i3))
                       )
| rooteq_factorize_par : forall (i1 i2 i3:Interaction),
                       (is_root_equivalent_directed
                           (interaction_alt (interaction_par i1 i2) (interaction_par i1 i3)) 
                           (interaction_par i1 (interaction_alt i2 i3))
                       )
(* ================================================================================== *)
| rooteq_loop_simpl : forall (sk:ScheduleKind),  
                     (is_root_equivalent_directed
                           (interaction_loop sk interaction_empty) 
                           interaction_empty
                       )
| rooteq_loop_unnest : forall (s1 s2:ScheduleKind) (i:Interaction),  
                     (is_root_equivalent_directed
                           (interaction_loop s1 (interaction_loop s2 i)) 
                           (interaction_loop (min_schedule_kind s1 s2) i)
                       ).

(**
Let us now prove that those transformations preserve the semantics.
Given that we have defined them as directed transformations,
given i and i' two equivalent interactions,
we must prove two disctinct Lemmas:
- "root_equivalent_left_preserve_sem_de", which states that the semantics of i is included into that of i'
- "root_equivalent_right_preserve_sem_de", which states that the semantics of i' is included into that of i
**)

Lemma root_equivalent_left_preserve_sem_de (i i': Interaction) (t : Trace):
  (is_root_equivalent_directed i i')
  -> (sem_de i t)
  -> (sem_de i' t).
Proof.
intros.
dependent induction i.
- simpl in *. inversion H. symmetry in H0. destruct H0.
  simpl. reflexivity.
- simpl in *. inversion H. symmetry in H0. destruct H0.
  simpl. reflexivity.
- simpl in *. 
  destruct H0 as (t1,H0).
  destruct H0 as (t2,H0).
  destruct H0. destruct H1.
  dependent induction H.
  + simpl.
    exists t1. exists t2.
    split ; try split ; try assumption.
  + simpl in H0.
    symmetry in H0. destruct H0. simpl in H2.
    destruct H2. assumption.
  + simpl in H1.
    symmetry in H1. destruct H1.
    rewrite app_nil_r in H2. 
    destruct H2. assumption.
  + simpl in H0.
    destruct H0 as (t1A,H0).
    destruct H0 as (t1B,H0).
    destruct H0. destruct H0.
    simpl.
    exists t1A. exists (t1B++t2).
    split.
    { assumption. }
    { split.
      - exists t1B. exists t2.
        split ; try split ; try assumption ; try reflexivity.
      - symmetry in H2. destruct H2. 
        symmetry in H3. destruct H3.
        simpl. rewrite app_assoc.
        reflexivity.
    }
- simpl in *. destruct H0 as (t1,H0).
  destruct H0 as (t2,H0).
  destruct H0. destruct H1.
  dependent induction H.
  + simpl.
    exists t1. exists t2.
    split ; try split ; try assumption.
  + simpl in H0. symmetry in H0. destruct H0.
    apply is_weak_seq_nil_prop2 in H2.
    destruct H2.
    assumption.
  + simpl in H1.
    symmetry in H1. destruct H1.
    apply is_weak_seq_nil_prop3 in H2.
    destruct H2.
    assumption.
  + simpl in H0.
    destruct H0 as (t1A,H0).
    destruct H0 as (t1B,H0).
    destruct H0. destruct H0.
    simpl.
    exists t1A.
    assert (exists tm : Trace, is_weak_seq t1B t2 tm /\ is_weak_seq t1A tm t).
    { apply (is_weak_seq_left_associativity t1 t1A t1B t2 t). split ; assumption. }
    destruct H4 as (tm,H4). destruct H4.
    exists tm.
    split.
    { assumption. }
    { split.
      - exists t1B. exists t2.
        split ; try split ; assumption.
      - assumption.
    }
- simpl in H0. destruct H0 as (t1,H0).
  destruct H0 as (t2,H0).
  destruct H0. destruct H1.
  dependent induction H.
  + simpl.
    exists t1. exists t2.
    split ; try split ; try assumption.
  + simpl in H0. 
    symmetry in H0. destruct H0.
    apply is_interleaving_nil_prop2 in H2.
    destruct H2.
    assumption.
  + simpl in H1.
    symmetry in H1. destruct H1.
    apply is_interleaving_nil_prop3 in H2.
    destruct H2.
    assumption.
  + simpl in H0.
    destruct H0 as (t1A,H0).
    destruct H0 as (t1B,H0).
    destruct H0. destruct H0.
    simpl.
    exists t1A.
    assert (exists tm : Trace, is_interleaving t1B t2 tm /\ is_interleaving t1A tm t).
    { apply (is_interleaving_left_associativity t1 t1A t1B t2 t). split ; assumption. }
    destruct H4 as (tm,H4). destruct H4.
    exists tm.
    split.
    { assumption. }
    { split.
      - exists t1B. exists t2.
        split ; try split ; assumption.
      - assumption.
    }
  + simpl. exists t2. exists t1.
    split ; try split.
    * apply IHi2.
      { apply rooteq_self. }
      { assumption. }
    * apply IHi1.
      { apply rooteq_self. }
      { assumption. }
    * apply is_interleaving_symmetry.
      assumption.
- dependent induction H.
  + assumption.
  + simpl in H0.
    destruct H0.
    { destruct H.
      - simpl. left. assumption.
      - simpl. right. left. assumption.
    } 
    { simpl. right. right. assumption. }
  + simpl in H0.
    destruct H0.
    { simpl. right. assumption. } 
    { simpl. left. assumption. }
  + simpl in H0.
    destruct H0.
    { simpl. assumption. }
    { assumption. }
  + simpl in H0.
    destruct H0.
    { destruct H as (t1,H0).
      destruct H0 as (t2,H0).
      destruct H0. destruct H0.
      simpl. exists t1. exists t2.
      split.
      - assumption.
      - split.
        + left. assumption.
        + assumption.
    }
    { destruct H as (t1,H0).
      destruct H0 as (t2,H0).
      destruct H0. destruct H0.
      simpl. exists t1. exists t2.
      split.
      - assumption.
      - split.
        + right. assumption.
        + assumption.
    }
  + simpl in H0.
    destruct H0.
    { destruct H as (t1,H0).
      destruct H0 as (t2,H0).
      destruct H0. destruct H0.
      simpl. exists t1. exists t2.
      split.
      - assumption.
      - split.
        + left. assumption.
        + assumption.
    }
    { destruct H as (t1,H0).
      destruct H0 as (t2,H0).
      destruct H0. destruct H0.
      simpl. exists t1. exists t2.
      split.
      - assumption.
      - split.
        + right. assumption.
        + assumption.
    }
  + simpl in H0.
    destruct H0.
    { destruct H as (t1,H0).
      destruct H0 as (t2,H0).
      destruct H0. destruct H0.
      simpl. exists t1. exists t2.
      split.
      - assumption.
      - split.
        + left. assumption.
        + assumption.
    }
    { destruct H as (t1,H0).
      destruct H0 as (t2,H0).
      destruct H0. destruct H0.
      simpl. exists t1. exists t2.
      split.
      - assumption.
      - split.
        + right. assumption.
        + assumption.
    }
- dependent induction H.
  + assumption.
  + simpl in H0.
    destruct H0 as (subs,H0).
    destruct H0.
    inversion H0.
    * simpl. reflexivity.
    * assert (In t_first subs).
      { rewrite <- H4. simpl. left. reflexivity. }
      apply H in H6. contradiction.
    * assert (In t_first subs).
      { rewrite <- H5. simpl. left. reflexivity. }
      apply H in H7. contradiction.
    * assert (In t_first subs).
      { rewrite <- H5. simpl. left. reflexivity. }
      apply H in H7. contradiction.
  + apply sem_de_loop_max_schedule_inclusion.
    assumption.
Qed.

Lemma root_equivalent_right_preserve_sem_de (i i': Interaction) (t : Trace):
  (is_root_equivalent_directed i i')
  -> (sem_de i' t)
  -> (sem_de i t).
Proof.
intros.
dependent induction i.
- inversion H. destruct H2.
  simpl in H0. simpl. assumption. 
- inversion H. destruct H2.
  simpl in H0. simpl. assumption.
- dependent induction H.
  + assumption.
  + simpl. exists nil. exists t.
    split ; try split.
    * assumption.
    * simpl. reflexivity.
  + simpl. exists t. exists nil.
    split ; try split.
    * assumption.
    * reflexivity.
    * rewrite app_nil_r. reflexivity.
  + simpl in H0.
    destruct H0 as (t1,H0).
    destruct H0 as (t2,H0).
    destruct H0.
    destruct H0.
    destruct H0 as (t2A,H0).
    destruct H0 as (t2B,H0).
    destruct H0.
    destruct H2.
    simpl. exists (t1 ++ t2A). exists t2B.
    split.
    { exists t1. exists t2A.
      split ; try split.
      - assumption.
      - assumption.
      - reflexivity.
    }
    { split.
      - assumption.
      - rewrite <- app_assoc. 
        rewrite <- H3. assumption.
    }
- dependent induction H.
  + assumption.
  + simpl. exists nil. exists t.
    split ; try split.
    * assumption.
    * apply weak_seq_nil_left.
  + simpl. exists t. exists nil.
    split ; try split.
    * assumption.
    * reflexivity.
    * apply weak_seq_nil_right.
  + simpl in H0.
    destruct H0 as (t1,H0).
    destruct H0 as (t2,H0).
    destruct H0.
    destruct H0.
    destruct H0 as (t2A,H0).
    destruct H0 as (t2B,H0).
    destruct H0.
    destruct H2.
    simpl.
    assert (exists tm : Trace, is_weak_seq t1 t2A tm /\ is_weak_seq tm t2B t).
    { apply (is_weak_seq_right_associativity t1 t2 t2A t2B t). split ; assumption. }
    destruct H4 as (tm,H4).
    destruct H4.
    exists tm. exists t2B.
    split.
    { exists t1. exists t2A.
      split ; try split ; try assumption.
    }
    { split ; assumption. }
- dependent induction H.
  + assumption.
  + simpl. exists nil. exists t.
    split ; try split.
    * assumption.
    * apply interleaving_nil_left.
  + simpl. exists t. exists nil.
    split ; try split.
    * assumption.
    * reflexivity.
    * apply interleaving_nil_right.
  + simpl in H0.
    destruct H0 as (t1,H0).
    destruct H0 as (t2,H0).
    destruct H0.
    destruct H0.
    destruct H0 as (t2A,H0).
    destruct H0 as (t2B,H0).
    destruct H0.
    destruct H2.
    simpl.
    assert (exists tm : Trace, is_interleaving t1 t2A tm /\ is_interleaving tm t2B t).
    { apply (is_interleaving_right_associativity t1 t2 t2A t2B t). split ; assumption. }
    destruct H4 as (tm,H4).
    destruct H4.
    exists tm. exists t2B.
    split.
    { exists t1. exists t2A.
      split ; try split ; try assumption.
    }
    { split ; assumption. }
  + simpl in H0.
    destruct H0 as (t2,H0).
    destruct H0 as (t1,H0).
    destruct H0.
    destruct H0.
    simpl. exists t1. exists t2.
    split ; try split.
    * assumption.
    * assumption.
    * apply is_interleaving_symmetry. assumption.
- dependent induction H.
  + assumption.
  + simpl. simpl in H0. destruct H0.
    { left. left. assumption. }
    { destruct H.
      - left. right. assumption.
      - right. assumption.
    }
  + simpl. simpl in H0.
    destruct H0.
    * right. assumption. 
    * left. assumption.
  + simpl. left. assumption.
  + simpl in H0.
    destruct H0 as (t1,H0).
    destruct H0 as (t2,H0).
    destruct H0. destruct H0.
    simpl. destruct H0.
    * left. exists t1. exists t2.
      split ; try split ; assumption.
    * right. exists t1. exists t2.
      split ; try split ; assumption.
  + simpl in H0.
    destruct H0 as (t1,H0).
    destruct H0 as (t2,H0).
    destruct H0. destruct H0.
    simpl. destruct H0.
    * left. exists t1. exists t2.
      split ; try split ; assumption.
    * right. exists t1. exists t2.
      split ; try split ; assumption.
  + simpl in H0.
    destruct H0 as (t1,H0).
    destruct H0 as (t2,H0).
    destruct H0. destruct H0.
    simpl. destruct H0.
    * left. exists t1. exists t2.
      split ; try split ; assumption.
    * right. exists t1. exists t2.
      split ; try split ; assumption.
- dependent induction H.
  + assumption.
  + simpl in H0. 
    symmetry in H0. destruct H0.
    simpl. exists nil.
    split.
    * intros. contradiction.
    * apply merge_zero.
  + apply sem_de_loop_max_schedule_inclusion.
    assumption.
Qed.


(**
** Reflexive and symmetric relation on the root of interactions

Now that we have defined some directed transformations that preserve the semantics in both directions,
we can define a relation that includes those transformations in both directions.

This is done in "is_root_equivalent".
**)

Inductive is_root_equivalent : Interaction -> Interaction -> Prop :=
| rooteq_direction1 : forall (i1 i2:Interaction),
                       (is_root_equivalent_directed i1 i2)
                       -> (is_root_equivalent i1 i2)
| rooteq_direction2 : forall (i1 i2:Interaction),
                       (is_root_equivalent_directed i1 i2)
                       -> (is_root_equivalent i2 i1).

(**
As a result "is_root_equivalent" is a relation:
- that is reflexive (proven in Lemma "root_equivalent_reflexivity").
- that is symmetric (proven in Lemma "root_equivalent_symmetry").
- that preserve the semantics (proven in Lemma "root_equivalent_preserve_sem_de")
**)

Lemma root_equivalent_reflexivity (i:Interaction) :
  (is_root_equivalent i i).
Proof.
apply rooteq_direction1.
apply rooteq_self.
Qed.

Lemma root_equivalent_symmetry (i1 i2:Interaction) :
  (is_root_equivalent i1 i2) <-> (is_root_equivalent i2 i1).
Proof.
split ; intros.
- dependent induction H.
  + apply rooteq_direction2. assumption.
  + apply rooteq_direction1. assumption.
- dependent induction H.
  + apply rooteq_direction2. assumption.
  + apply rooteq_direction1. assumption.
Qed.

Lemma root_equivalent_preserve_sem_de (i i':Interaction) (t:Trace) :
  (is_root_equivalent i i')
  -> ( (sem_de i t) <-> (sem_de i' t) ).
Proof.
intros.
split ; intros.
- dependent induction H.
  + apply (root_equivalent_left_preserve_sem_de i1 i2 t) ; assumption.
  + apply (root_equivalent_right_preserve_sem_de i1 i2 t) ; assumption.
- dependent induction H.
  + apply (root_equivalent_right_preserve_sem_de i1 i2 t) ; assumption.
  + apply (root_equivalent_left_preserve_sem_de i1 i2 t) ; assumption.
Qed.

(**
** Applying transformations inductively on inner sub-interactions and definition of the equivalence relation

Now that we have consolidated the definition of equivalent transformations that affect the root of interaction terms, let us
extend those transformations so that they can affect sub-interactions within interaction terms.

In "is_interaction_equivalent" we define such transformations inductively:
- the rule "root_eq" allows transformations on the root of interactions
- four rules allow the transformation of the left sub-interaction within an interaction which root is a binary constructor:
 - with "inteq_binary_induct_left_strict", if i1 can transform into i1' then strict(i1,i2) can transform into strict(i1',i2)
 - with "inteq_binary_induct_left_seq", if i1 can transform into i1' then seq(i1,i2) can transform into seq(i1',i2)
 - with "inteq_binary_induct_left_par", if i1 can transform into i1' then par(i1,i2) can transform into par(i1',i2)
 - with "inteq_binary_induct_left_alt", if i1 can transform into i1' then alt(i1,i2) can transform into alt(i1',i2)
- four rules allow the transformation of the right sub-interaction within an interaction which root is a binary constructor:
 - with "inteq_binary_induct_right_strict", if i2 can transform into i2' then strict(i1,i2) can transform into strict(i1,i2')
 - with "inteq_binary_induct_right_seq", if i2 can transform into i2' then seq(i1,i2) can transform into seq(i1,i2')
 - with "inteq_binary_induct_right_par", if i2 can transform into i2' then par(i1,i2) can transform into par(i1,i2')
 - with "inteq_binary_induct_right_alt", if i2 can transform into i2' then alt(i1,i2) can transform into alt(i1,i2')
- one rule allows the transformation of the unique sub-interaction within an interaction which root is a loop constructor:
 - with "inteq_unary_induct_loop", if i1 can transform into i1' then loop_s(i1) can transform into loop_s(i1') for any ScheduleKind s

In addition to those rules, which allow the extension of the transformations to sub-terms within interactions, we also add a
"inteq_transitivity" rule which make the relation transitive:
- "inteq_transitivity" implies that if i1 can be transformed into i2 and if i2 can be transformed into i3 then it means that i1 can be transformed into i3   
**)

Inductive is_interaction_equivalent : Interaction -> Interaction -> Prop :=
| inteq_transitivity : forall (i1 i2 i3:Interaction),
                        (is_interaction_equivalent i1 i2)
                        -> (is_interaction_equivalent i2 i3)
                        -> (is_interaction_equivalent i1 i3)
(* ================================================================================== *)
| root_eq : forall (i1 i2:Interaction),
                     (is_root_equivalent i1 i2)
                     -> (is_interaction_equivalent i1 i2)
(* ================================================================================== *)
| inteq_binary_induct_left_strict : forall (i1 i1' i2:Interaction),
                     (is_interaction_equivalent i1 i1')
                     -> (is_interaction_equivalent 
                            (interaction_strict i1 i2)
                            (interaction_strict i1' i2)
                        )
| inteq_binary_induct_left_seq : forall (i1 i1' i2:Interaction),
                     (is_interaction_equivalent i1 i1')
                     -> (is_interaction_equivalent 
                            (interaction_seq i1 i2)
                            (interaction_seq i1' i2)
                        )
| inteq_binary_induct_left_par : forall (i1 i1' i2:Interaction),
                     (is_interaction_equivalent i1 i1')
                     -> (is_interaction_equivalent 
                            (interaction_par i1 i2)
                            (interaction_par i1' i2)
                        )
| inteq_binary_induct_left_alt : forall (i1 i1' i2:Interaction),
                     (is_interaction_equivalent i1 i1')
                     -> (is_interaction_equivalent 
                            (interaction_alt i1 i2)
                            (interaction_alt i1' i2)
                        )
(* ================================================================================== *)
| inteq_binary_induct_right_strict : forall (i1 i2 i2':Interaction),
                     (is_interaction_equivalent i2 i2')
                     -> (is_interaction_equivalent 
                            (interaction_strict i1 i2)
                            (interaction_strict i1 i2')
                        )
| inteq_binary_induct_right_seq : forall (i1 i2 i2':Interaction),
                     (is_interaction_equivalent i2 i2')
                     -> (is_interaction_equivalent 
                            (interaction_seq i1 i2)
                            (interaction_seq i1 i2')
                        )
| inteq_binary_induct_right_par : forall (i1 i2 i2':Interaction),
                     (is_interaction_equivalent i2 i2')
                     -> (is_interaction_equivalent 
                            (interaction_par i1 i2)
                            (interaction_par i1 i2')
                        )
| inteq_binary_induct_right_alt : forall (i1 i2 i2':Interaction),
                     (is_interaction_equivalent i2 i2')
                     -> (is_interaction_equivalent 
                            (interaction_alt i1 i2)
                            (interaction_alt i1 i2')
                        )
(* ================================================================================== *)
| inteq_unary_induct_loop : forall (i1 i1':Interaction) (sk:ScheduleKind), 
                     (is_interaction_equivalent i1 i1')
                     -> (is_interaction_equivalent 
                            (interaction_loop sk i1)
                            (interaction_loop sk i1')
                        ).

(**
Now that we have defined our relation, let us prove that is is indeed an equivalence relation. For that it needs to be reflexive, symmetric and transitive.
We prove that in the Lemmas:
- "interaction_equivalent_reflexivity" for the reflexivity
- "interaction_equivalent_symmetry" for the symmetry
- while the transitivity is ensured by the rule "inteq_transitivity" in the definition
**)

Lemma interaction_equivalent_reflexivity (i: Interaction) :
  (is_interaction_equivalent i i).
Proof.
intros.
apply root_eq.
apply root_equivalent_reflexivity.
Qed.

Lemma interaction_equivalent_is_symmetric1 (i i': Interaction) :
  (is_interaction_equivalent i i')
  -> (is_interaction_equivalent i' i).
Proof.
intros.
dependent induction H.
- apply (inteq_transitivity i3 i2 i1) ; assumption.
- apply root_eq. apply root_equivalent_symmetry. assumption.
- apply inteq_binary_induct_left_strict.
  assumption.
- apply inteq_binary_induct_left_seq.
  assumption.
- apply inteq_binary_induct_left_par.
  assumption.
- apply inteq_binary_induct_left_alt.
  assumption.
- apply inteq_binary_induct_right_strict.
  assumption.
- apply inteq_binary_induct_right_seq.
  assumption.
- apply inteq_binary_induct_right_par.
  assumption.
- apply inteq_binary_induct_right_alt.
  assumption.
- apply inteq_unary_induct_loop.
  assumption.
Qed.

Lemma interaction_equivalent_symmetry (i i': Interaction) :
  (is_interaction_equivalent i i')
  <-> (is_interaction_equivalent i' i).
split ; intros ;
apply interaction_equivalent_is_symmetric1 ; assumption.
Qed.

(**
Finally, we prove that if any two interactions are equivalent as per this equivalence relation, then they must have the same semantics.

To do so, we proceed in two steps:
- with "interaction_equivalent_left_preserve_sem_de" we at first prove that if i is equivalent to i', then the semantics of i is included into that of i'
- then, given that the relation is symmetric, the other inclusion is immediate
**)

Lemma interaction_equivalent_left_preserve_sem_de (i i': Interaction) (t : Trace):
  (is_interaction_equivalent i i')
  -> (sem_de i t)
  -> (sem_de i' t).
Proof.
intros.
dependent induction H generalizing t.
- apply IHis_interaction_equivalent2.
  apply IHis_interaction_equivalent1.
  assumption.
- apply (root_equivalent_preserve_sem_de i1 i2) ; assumption.
- simpl in H0.
  destruct H0 as (t1,H0).
  destruct H0 as (t2,H0).
  destruct H0 as (H1,H0).
  destruct H0 as (H2,H0).
  simpl.
  exists t1. exists t2.
  split ; try split.
  + apply IHis_interaction_equivalent. 
    assumption.
  + assumption.
  + assumption.
- simpl in H0.
  destruct H0 as (t1,H0).
  destruct H0 as (t2,H0).
  destruct H0 as (H1,H0).
  destruct H0 as (H2,H0).
  simpl.
  exists t1. exists t2.
  split ; try split.
  + apply IHis_interaction_equivalent. 
    assumption.
  + assumption.
  + assumption.
- simpl in H0.
  destruct H0 as (t1,H0).
  destruct H0 as (t2,H0).
  destruct H0 as (H1,H0).
  destruct H0 as (H2,H0).
  simpl.
  exists t1. exists t2.
  split ; try split.
  + apply IHis_interaction_equivalent. 
    assumption.
  + assumption.
  + assumption.
- simpl in H0.
  destruct H0.
  + simpl. left.
    apply IHis_interaction_equivalent.
    assumption.
  + simpl. right.
    assumption.
- simpl in H0.
  destruct H0 as (t1,H0).
  destruct H0 as (t2,H0).
  destruct H0 as (H1,H0).
  destruct H0 as (H2,H0).
  simpl.
  exists t1. exists t2.
  split ; try split.
  + assumption.
  + apply IHis_interaction_equivalent. 
    assumption.
  + assumption.
- simpl in H0.
  destruct H0 as (t1,H0).
  destruct H0 as (t2,H0).
  destruct H0 as (H1,H0).
  destruct H0 as (H2,H0).
  simpl.
  exists t1. exists t2.
  split ; try split.
  + assumption.
  + apply IHis_interaction_equivalent. 
    assumption.
  + assumption.
- simpl in H0.
  destruct H0 as (t1,H0).
  destruct H0 as (t2,H0).
  destruct H0 as (H1,H0).
  destruct H0 as (H2,H0).
  simpl.
  exists t1. exists t2.
  split ; try split.
  + assumption.
  + apply IHis_interaction_equivalent. 
    assumption.
  + assumption.
- simpl in H0.
  destruct H0.
  + simpl. left.
    assumption.
  + simpl. right.
    apply IHis_interaction_equivalent.
    assumption.
- simpl in H0.
  destruct H0 as (subs,H0).
  destruct H0.
  simpl. exists subs.
  split.
  + intros. apply IHis_interaction_equivalent.
    apply H0. assumption.
  + assumption.
Qed.

(**
Theorem "interaction_equivalent_preserve_sem_de" concludes this proof,
stating that if two interactions i and i' are equivalent according to the aformentioned equivalence relation,
then they have the exact same semantics
**)

Theorem interaction_equivalent_preserve_sem_de (i i': Interaction) (t : Trace):
  (is_interaction_equivalent i i')
  -> ( (sem_de i t) <-> (sem_de i' t) ).
Proof.
intros.
split.
- apply interaction_equivalent_left_preserve_sem_de. assumption.
- apply interaction_equivalent_left_preserve_sem_de.
  apply interaction_equivalent_symmetry.
  assumption.
Qed. 



