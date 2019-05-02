Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.

Open Scope type_scope.
Open Scope string_scope.

(* First we define lexes, which are building blocks for lexemes. These
are not lexemes themselves because we require additional structure to
develop a notion of derivational relationships. *)

Inductive lex : Set :=
| OS : lex (* father *)
| NESHNABÉ : lex (* person *)
| BIWABEK : lex (* metal *)
| MOWECH : lex (* feces *)
| BAGJÉʔGEN : lex. (* pool cue *)

(* Here we define the only derivational relationship that we are
concerned with for this fragment, IJ, which relates lexes to a lexeme
that is related by the function c to the class appropriate to
inalienably possessed nouns. *)

Inductive rel : Set :=
| IJ : rel. (* fellow *)

(* Lexemes are either simple, in the case of root or have a
relationship to a class of likewise derived lexemes in the case of
cmplx. *)

Inductive lexeme : Type :=
| root (l : lex)
| cmplx (r : rel) (l : lex).

(* The type mm is for atoms used in m-categories or mcats, which are
lists of mms. Here this is somewhat redundant because our fragment is
so simple. *)

Inductive mm : Set :=
| free : mm
| freem : mm
| bound : mm
| nposs : mm.

(* I define fclasses that are not used in this fragment. These are
related to lexemes by the function c. *)

Inductive fclass : Set :=
| long : fclass
| short : fclass
| nosuffix : fclass
| msuffix : fclass
| LN : fclass
| LM : fclass
| SN : fclass
| SM : fclass
| LNM : fclass
| LSN : fclass
| LSM : fclass
| SNM : fclass
| LSNM : fclass
| none : fclass. (* This will exist outside the order. *)

(* As stated above, mcat is a list of mms. An mform is a string. *)

Definition mcat := list mm.
Definition mform := string.

(* An mtrip is the data structure used to define Fentrys *)

Definition mtrip := mcat * mform * lexeme.

(* Note that the check below demonstrates why simply saying that we're
working with mtrips is not good enough. Non-grammatical triples
check. We need to be able to specify which are legal triples. *)

Check ([ SNM ] , "walk" , root OS).

(* To solve this I define a predicate Fentry, the use of which will be
seen below. Essentially, only grammatical mtrips will be Fentrys. *)

Axiom Fentry : mtrip -> Prop.

(* lem is the order over mcats. The axioms below define it as an
order. *)

Axiom lem : mcat -> mcat -> Prop.
Axiom lem_refl : forall x : mcat, lem x x.
Axiom lem_antisym : forall x y : mcat, lem x y -> lem y x -> x = y.
Axiom lem_trans : forall x y z : mcat, lem x y -> lem y z -> lem x z.

(* The order is not natural. We define, explicitly, the relation. *)

Axiom free_lem_bound : lem [ free ] [ bound ].
Axiom free_lem_freem : lem [ free ] [ freem ].

(* lef is the order over fclasses. The axioms below define it as an
order. *)

Axiom lef : fclass -> fclass -> Prop.
Axiom lef_refl : forall x : fclass, lef x x.
Axiom lef_antisym : forall x y : fclass, lef x y -> lef y x -> x = y.
Axiom lef_trans : forall x y z : fclass, lef x y -> lef y z -> lef x z.

(* The order is not natural. We define, explicitly, the relation. *)

Axiom ln_lef_long : lef LN long.
Axiom lm_lef_long : lef LM long.
Axiom ln_lef_nosuffix : lef LN nosuffix.
Axiom sn_lef_nosuffix : lef SN nosuffix.
Axiom lm_lef_msuffix : lef LM msuffix.
Axiom sm_lef_msuffix : lef SM msuffix.
Axiom sn_lef_short : lef SN short.
Axiom sm_lef_short : lef SM short.
Axiom lnm_lef_ln : lef LNM LN.
Axiom lsn_lef_ln : lef LSN LN.
Axiom lnm_lef_lm : lef LNM LM.
Axiom lsm_lef_lm : lef LSM LM.
Axiom lsn_lef_sn : lef LSN SN.
Axiom snm_lef_sn : lef SNM SN.
Axiom lsm_lef_sm : lef LSM SM.
Axiom snm_lef_sm : lef SNM SM.
Axiom lsnm_lef_lnm : lef LSNM LNM.
Axiom lsnm_lef_lsm : lef LSNM LSM.

(* Below we define c which relates lexemes to their fclass. We assume
that only cmplx IJ NESHNABÉ will have an fclass that allows for the
derivation from root NESHNABÉ as this is the only attested lexeme for
that derivation among the lexemes defined. *)

Definition c (l:lexeme) : fclass :=
  match l with
  | root OS => SN
  | root NESHNABÉ => LM
  | root BIWABEK => LSM (* We'd predict LSNM but these are attested. *)
  | root BAGJÉʔGEN => SNM (* The same as above. *)
  | root MOWECH => LSNM (* There are missing forms here too. *)
  | cmplx IJ lx => match lx with
                   | NESHNABÉ => SN
                   | _ => none
                   end
  end.

(* Below I define the form building functions. These ignore the
intricacies of providing correct surface forms as a simplification and
due to a lack of the specification of a phonological interface. *)

Definition suffix_m (s:mform) : mform :=
  s ++ "m".

Definition prefix_n (s:mform) : mform :=
  "n" ++ s.

Definition prefix_ned (s:mform) : mform :=
  "ned" ++ s.

Definition prefix_ij (s:mform) : mform :=
  "ij" ++ s.

(* These are definitions of basic stems for the lexemes above. Note
that I define the mtrips first and then specify that they are
Fentrys. *)

Definition mowech_free := ([ free ], "mowech", root MOWECH) : mtrip.

Definition os_bound := ([ bound ], "os", root OS) : mtrip.

Axiom f_mowech_free : Fentry mowech_free.

(* f_m is the rule for specifying that... *)

Axiom f_m : forall (mt : mtrip), (Fentry mt) -> (lem (fst (fst mt)) [ freem ]) -> (lef (c (snd mt)) msuffix) -> Fentry ([ bound ], suffix_m (snd (fst mt)), (snd mt)).

Axiom f_n : forall (mt : mtrip), (Fentry mt) -> (lem (fst (fst mt)) [ bound ]) -> (lef (c (snd mt)) short) -> Fentry ([ nposs ], prefix_n (snd (fst mt)), (snd mt)).

Axiom f_ned : forall (mt : mtrip), (Fentry mt) -> (lem (fst (fst mt)) [ bound ]) -> (lef (c (snd mt)) long) -> Fentry ([ nposs ], prefix_ned (snd (fst mt)), (snd mt)).

Definition glex (l:lexeme) :=
  match l with
  | root lx => lx
  | cmplx _ lx => lx
  end.
  
Axiom f_ij : forall (mt : mtrip), (Fentry mt) -> (lem (fst (fst mt)) [ freem ]) -> (lef (c (snd mt)) msuffix) -> Fentry ([ bound ], prefix_ij (snd (fst mt)), cmplx IJ (glex (snd mt))).

Lemma walk_base_is_fentry:
  Fentry mowech_free.
Proof.
  apply f_mowech_free.
Qed.

Lemma mowech_free_is_free:
  lem (fst (fst mowech_free)) [ free ].
Proof.
  simpl.
  apply lem_refl.
Qed.

Lemma mowech_free_is_LSNM:
  lef (c (snd mowech_free)) LSNM.
Proof.
  simpl.
  apply lef_refl.
Qed.

Lemma LM_is_msuffix:
  lef LM msuffix.
Proof.
  apply lm_lef_msuffix.  
Qed.

Lemma LNM_is_msuffix:
  lef LNM msuffix.
Proof.
  assert (H1 : lef LNM LM).
  { apply lnm_lef_lm. }
  assert (H2 : lef LM msuffix).
  { apply lm_lef_msuffix. }
  apply (lef_trans LNM LM msuffix H1 H2).
Qed.

Lemma mowech_free_is_msuffix:
  lef (c (snd mowech_free)) msuffix.
Proof.
  simpl.
  assert (H1 : lef LSNM LNM).
  { apply lsnm_lef_lnm. }
  assert (H2 : lef LNM msuffix).
  { exact LNM_is_msuffix. }
  apply (lef_trans LSNM LNM msuffix H1 H2).
Qed.

Example test_f_m:
  Fentry ([ bound ], "mowechm", root MOWECH).
Proof.
  assert (H1 : lem [ free ] [ freem ]).
  { apply free_lem_freem. }
  assert (H2 : lef LSNM msuffix).
  { exact mowech_free_is_msuffix. }
  apply (f_m mowech_free).
  exact f_mowech_free.
  simpl.
  assumption.
  simpl.
  assumption.
Qed.
