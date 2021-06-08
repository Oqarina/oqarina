Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.Morphisms.


From ReductionEffect Require Import PrintingEffect.

Require Import identifiers.
Require Import properties.

(*! Type Checking *)

Inductive in_enumR (id : identifier) (t : property_type) : Prop :=
| In_Enum (literals : list identifier) :
    t = PT_Enumeration literals ->
    In id literals -> in_enumR id t.

Definition in_enum (id : identifier) (t : property_type) : bool  :=
  match t with
  | PT_Enumeration literals => existsb (identifier_beq id) literals
  | _ => false
  end.

Lemma in_enum_iff : forall id l,
    in_enum id (PT_Enumeration l) = true <-> in_enumR id (PT_Enumeration l).
Proof.
  unfold in_enum.
  induction l as [|i l'].
  - simpl. split.
    + intros. discriminate.
    + intros. inversion H. inversion H0; subst. inversion H1.
  - simpl. split.
    + destruct (id_beqP id i) as [H1 | H1].
      * intros. subst. econstructor. reflexivity.
        simpl. auto.
      * simpl. intros. apply IHl' in H. econstructor. reflexivity. right.
        destruct H. inversion H; subst. assumption.
    + destruct (id_beqP id i) as [H1 | H1].
      * auto.
      * intros. rewrite IHl'. apply (In_Enum id (PT_Enumeration l') l'). reflexivity.
        inversion H; clear H. inversion H0; subst; clear H0.
        destruct H2. rewrite H in H1. contradiction.
        apply H.
Qed.

Inductive is_unitR (id : identifier) (unit : unit_literal) : Prop :=
| Is_Base :
    unit = BaseUnit id -> is_unitR id unit
| Is_Derived base_id factor :
    unit = DerivedUnit id base_id factor -> is_unitR id unit.

Definition is_unit (id : identifier) (unit : unit_literal) : bool :=
  match unit with
  | BaseUnit uid
  | DerivedUnit uid _ _ => identifier_beq uid id
  end.

Lemma is_unit_iff : forall id unit,
    is_unit id unit = true <-> is_unitR id unit.
Proof.
  intros.
  split; intros H.
  - destruct unit; simpl in H.
    + apply Is_Base.
      destruct (id_beqP name id).
      * rewrite e. auto.
      * discriminate.
    + apply (Is_Derived _ _ base factor).
      destruct (id_beqP name id).
      * rewrite e. auto.
      * discriminate.
  - destruct unit; simpl.
    + inversion H. injection H0. intros.
      destruct (id_beqP name id).
      * reflexivity.
      * contradiction.
      * discriminate.
    + inversion H.
      * discriminate.
      * injection H0. intros.
        destruct (id_beqP name id).
        -- reflexivity.
        -- contradiction.
Qed.

Definition in_unitsR (id : identifier) (t : property_type) : Prop :=
  match t with
  | PT_Units units => Exists (is_unitR id) units
  | PT_Number _ _ None => False
(*  | NumberType _ (Some units) => Exists (Is_Unit_Id id) units *)
  | _ => False
  end.

Definition in_units (id : identifier) (t : property_type) : bool :=
  match t with
  | PT_Units units => existsb (is_unit id) units
  | PT_Number _ _ None => false
(*  | NumberType _ (Some units) => Exists (Is_Unit_Id id) units *)
  | _ => false
  end.

Lemma exP : forall {A} (f : A -> bool)  l,
    existsb f l = true <-> Exists (fun x => f x = true) l.
Proof.
  split.
  - generalize dependent f. induction l.
    + simpl. intros. discriminate.
    + simpl. intros. destruct (f a) eqn:Ef.
      * constructor. apply Ef.
      * simpl in H. apply IHl in H.
        apply Exists_cons_tl. auto.
  - generalize dependent f. induction l.
    + intros. apply Exists_nil in H. contradiction.
    + intros. destruct (f a) eqn:Ef.
      * simpl. rewrite Ef. auto.
      * simpl. rewrite Ef. apply IHl.
        apply Exists_cons in H. rewrite Ef in H. destruct H.
        discriminate. auto.
Qed.

Lemma in_units_iff : forall id t,
    in_units id t = true <-> in_unitsR id t.
Proof.
  split.
  - destruct t; try discriminate.
    + simpl. intros H. rewrite exP in H.
      induction units.
      * inversion H.
      * inversion H; subst.
        -- apply Exists_cons_hd. apply is_unit_iff.
           assumption.
        -- apply Exists_cons_tl. apply IHunits.
           assumption.
    + intro H. destruct units; discriminate.
  - destruct t; simpl; auto.
    + intros H. apply exP.
      induction units.
      * inversion H.
      * inversion H; subst.
        -- apply Exists_cons_hd. apply is_unit_iff.
           assumption.
        -- apply Exists_cons_tl. apply IHunits.
           assumption.
    + destruct units; auto.
Qed.

Definition is_declR (id : identifier) (d' : property_set_declaration) (d : property_set_declaration) : Prop :=
  match d with
  | PropertyTypeDecl id' _
  | PropertyConstantDecl id' _ _
  | PropertyDecl id' _ _ _ => id' = id /\ d' = d
  end.

Definition is_decl (id : identifier) (d : property_set_declaration) : option property_set_declaration :=
  match d with
  | PropertyTypeDecl id' t
  | PropertyConstantDecl id' t _
  | PropertyDecl id' t _ _ => if identifier_beq id' id then Some d else None
  end.

Lemma is_decl_iff: forall d id t,
    is_decl id d = Some t <-> is_declR id t d.
Proof.
  split.
  - intros H. destruct d; simpl in H; try discriminate.
    + simpl. destruct (identifier_beq name id) eqn:D.
      * apply identifier_beq_eq in D. injection H. intros H0. auto.
      * discriminate H.
    + simpl. destruct (identifier_beq name id) eqn:D.
      * apply identifier_beq_eq in D. injection H. intros H0. auto.
      * discriminate H.
    + simpl. destruct (identifier_beq name id) eqn:D.
      * apply identifier_beq_eq in D. injection H. intros H0. auto.
      * discriminate H.
  - intros H. destruct d; simpl in H; try contradiction.
    + simpl. destruct H. apply identifier_beq_eq in H. rewrite H, H0. reflexivity.
    + simpl. destruct H. apply identifier_beq_eq in H. rewrite H, H0. reflexivity.
    + simpl. destruct H. apply identifier_beq_eq in H. rewrite H, H0. reflexivity.
Qed.

Definition in_propertysetR (id : identifier) (d : property_set_declaration) (mu : model_unit) : Prop :=
  let 'PropertySet id' decls := mu in
  Exists (is_declR id d) decls.

Definition in_propertyset (id : identifier) (mu : model_unit) : option property_set_declaration :=
  let 'PropertySet _ decls := mu in
  fold_left (fun (o : option property_set_declaration) d => if o then o else is_decl id d)
            decls None.

Lemma find_first1 : forall id ds p,
    fold_left
      (fun (o : option property_set_declaration) (d : property_set_declaration) =>
         if o then o else is_decl id d) ds (Some p) = Some p.
Proof.
  induction ds.
  - simpl. reflexivity.
  - intros. simpl. apply IHds.
Qed.

(* Exists could give any of several occurrences, for the function we
   ignore later occurrences. Need to add something about uniqueness
   of names in property sets. *)

Axiom exists_unique : forall id t d ds,
  Exists (is_declR id t) (d :: ds) ->
  Exists (is_declR id t) ds ->
  is_decl id d = None.

Lemma in_propertyset_iff : forall id t mu,
    in_propertyset id mu = Some t <-> in_propertysetR id t mu.
Proof.
  split.
  - destruct mu.
    generalize dependent t.
    induction declarations as [| decl decls' IHd'].
    + simpl. discriminate.
    + intros. simpl.
      destruct (is_decl id decl) eqn:Ed.
      * apply Exists_cons_hd.
        apply is_decl_iff.
        unfold in_propertyset in H.
        simpl in H.
        rewrite Ed in H.
        rewrite find_first1 in H.
        rewrite H in Ed. apply Ed.
      * apply Exists_cons_tl.
        unfold in_propertyset in H. simpl in H.
        rewrite Ed in H.
        apply IHd' in H. apply H.
  - destruct mu.
    generalize dependent t.
    induction declarations as [| decl decls' IHd'].
    + simpl. intros. inversion H.
    + intros. simpl in H |- *.
      inversion H; subst.
      * apply is_decl_iff in H1.
        rewrite H1. apply find_first1.
      * inversion H; subst.
        -- apply is_decl_iff in H2.
           rewrite H2. apply find_first1.
        -- apply (exists_unique id t decl decls') in H.
           rewrite H.
           apply IHd' in H2. apply H2.
           apply H2.
Qed.

Definition is_psR (setid : identifier) (mu : model_unit) : Prop :=
  let 'PropertySet id _ := mu in
  id = setid.

Definition is_ps (setid : identifier) (mu : model_unit) : bool :=
  let 'PropertySet id _ := mu in
  identifier_beq id setid.

Lemma is_ps_iff : forall id mu,
    is_ps id mu = true <-> is_psR id mu.
Proof.
  split; intros.
  - destruct mu.
    simpl in H |- *.
    apply identifier_beq_eq. assumption.
  - destruct mu.
    simpl in H |- *.
    apply identifier_beq_eq. assumption.
Qed.

Definition in_modelR (setid id : identifier) (d : property_set_declaration) (m : aadl_model) : Prop :=
  let 'Model model_units := m in
  Exists (fun mu => is_psR setid mu /\ in_propertysetR id d mu)
         model_units.

Definition in_model (m : aadl_model) (setid id: identifier) : option property_set_declaration :=
  let 'Model model_units := m in
  fold_left (fun (o : option property_set_declaration) mu =>
               if o then o else in_propertyset id mu)
            (filter (is_ps setid) model_units) None.

(* Check that a type reference is resolved to a type *)
Definition is_resolved_typeR (m : aadl_model) (qname : ps_qname) (t: property_type) : Prop :=
  let 'PSQN setname name := qname in
  exists d, in_modelR (Id setname) (Id name) d m /\ d = PropertyTypeDecl (Id name) t.

(* Check that a reference to a property or constant is resolved to one of these *)
Definition is_resolved_valueR (m : aadl_model) (qname : ps_qname) (t : property_type) : Prop :=
  let 'PSQN setname name := qname in
  exists decl, in_modelR (Id setname) (Id name) decl m /\ (
            (exists val, decl = PropertyConstantDecl (Id name) t val) \/
            (exists def app, decl = PropertyDecl (Id name) t def app)
          ).

Fixpoint resolve_type' (fuel : nat) (m : aadl_model) (t : property_type) : option property_type :=
  match fuel with
  | 0%nat => None
  | S n => match t with
          | PT_TypeRef (PSQN setname name) =>
            match in_model m (Id setname) (Id name) with
            | Some decl => match decl with
                          | PropertyTypeDecl _ r => resolve_type' n m r
                          | _ => None
                          end
            | _ => None
            end
          | _ => Some t
          end
  end.

Definition resolve_type := resolve_type' 10.

Definition resolve_value (m : aadl_model) (qname : ps_qname) : option property_type :=
  let 'PSQN setname name := qname in
  match in_model m (Id setname) (Id name) with
  | Some decl => match decl with
                | PropertyConstantDecl _ r _
                | PropertyDecl _ r _ _ => resolve_type m r
                | _ => None
                end
  | _ => None
  end.

Reserved Notation "m '|-' t1 '==' t2" (at level 60, t1, t2 at next level).

Inductive same_typeR (m : aadl_model) (t t' : property_type) : Prop :=
| ST_TypeRef0 (qname1 qname2 : ps_qname) :
    t = PT_TypeRef qname1 ->
    t' = PT_TypeRef qname2 ->
    qname1 = qname2 -> m |- t == t'
| ST_TypeRef1 (qname : ps_qname) (r : property_type) :
    t = PT_TypeRef qname ->
    is_resolved_typeR m qname r ->
    same_typeR m r t' -> m |- t == t'
| ST_TypeRef2 (qname : ps_qname) (r : property_type) :
    t' = PT_TypeRef qname ->
    is_resolved_typeR m qname r ->
    m |- t == r -> m |- t == t'
| ST_Bool :
    t = aadlboolean ->
    t' = aadlboolean -> m |- t == t'
| ST_String :
    t = aadlstring ->
    t' = aadlstring -> m |- t == t'
| ST_Int :
    t = aadlinteger ->
    t' = aadlinteger -> m |- t == t'
| ST_Real :
    t = aadlreal ->
    t' = aadlreal -> m |- t == t'
where "m '|-' t1 '==' t2" := (same_typeR m t1 t2).

Reserved Notation "m '|-' v '∈' t" (at level 60, v at next level).

Inductive has_typeR (m : aadl_model) (t : property_type) (v : property_value) : Prop :=
| HT_PropertyRef (qname : ps_qname) (r : property_type) :
    v = PV_PropertyRef qname ->
    is_resolved_valueR m qname r ->
    m |- t == r -> m |- v ∈ t
| HT_TypeRef (qname : ps_qname) (r : property_type) :
    t = PT_TypeRef qname ->
    is_resolved_typeR m qname r ->
    m |- v ∈ r -> m |- v ∈ t
| HT_Bool (b : bool) :
    t = aadlboolean ->
    v = PV_Bool b -> m |- v ∈ t
| HT_String (s : string) :
    t = aadlstring ->
    v = PV_String s -> m |- v ∈ t
| HT_Enum (i : identifier) :
    v = PV_Enum i ->
    in_enumR i t -> m |- v ∈ t
| HT_Unit (i : identifier) :
    v = PV_Unit i ->
    in_unitsR i t -> m |- v ∈ t
| HT_Int (n : INT) :
    t = aadlinteger ->
    v = PV_Int n -> m |- v ∈ t
| HT_Int' (n : INT) :
    t = PT_Number aadlinteger None None ->
    v = PV_Int n -> m |- v ∈ t
| HT_Real (r : REAL) :
    t = aadlreal ->
    v = PV_Real r -> m |- v ∈ t
| HT_Real' (r : REAL) :
    t = PT_Number aadlreal None None ->
    v = PV_Real r -> m |- v ∈ t
| HT_IntU (n : INT) (rc : option range_constraint) (ut: property_type) (u : property_value) :
    t = PT_Number aadlinteger rc (Some ut) ->
    v = PV_IntU n u ->
    m |- u ∈ ut -> m |- v ∈ t
| HT_RealU (r : REAL) (rc : option range_constraint) (ut: property_type) (u : property_value) :
    t = PT_Number aadlreal rc (Some ut) ->
    v = PV_RealU r u ->
    has_typeR m t u -> has_typeR m t v
| HT_IntRange (min max : property_value) :
    t = PT_Range aadlinteger ->
    v = PV_IntRange min max ->
    m |- min ∈ aadlinteger ->
    m |- max ∈ aadlinteger -> m |- v ∈ t
| HT_RealRange (min max : property_value) :
    t = PT_Range aadlreal ->
    v = PV_RealRange min max ->
    m |- min ∈ aadlreal ->
    m |- max ∈ aadlreal -> m |- v ∈ t
| HT_IntRangeD (bt : property_type) (min max Δ : property_value) :
    t = PT_Range aadlinteger ->
    v = PV_IntRangeD min max Δ ->
    m |- min ∈ aadlinteger ->
    m |- max ∈ aadlinteger ->
    m |- Δ ∈ aadlinteger -> m |- v ∈ t
| HT_RealRangeD (bt : property_type) (min max Δ : property_value) :
    t = PT_Range aadlreal ->
    v = PV_RealRangeD min max Δ ->
    m |- min ∈ aadlreal ->
    m |- max ∈ aadlreal ->
    m |- Δ ∈ aadlreal -> m |- v ∈ t
| HT_Classifier :
    t = PT_Classifier ->
    v = PV_Classifier -> m |- v ∈ t
| HT_ModelRef (path : list identifier) :
    t = PT_Reference ->
    v = PV_ModelRef path -> m |- v ∈ t
| HT_Record_nil fdecls:
    t = PT_Record fdecls ->
    v = PV_Record [] -> m |- v ∈ t
| HT_Record_hd did ft fdecls vid fv fvals:
    t = PT_Record (FieldDecl did ft :: fdecls) ->
    v = PV_Record (FieldVal vid fv :: fvals) ->
    did = vid ->
    m |- fv ∈ ft ->
    m |- (PV_Record fvals) ∈ t -> m |- v ∈ t
| HT_Record_tl did ft fdecls fval fvals:
    t = PT_Record (FieldDecl did ft :: fdecls) ->
    v = PV_Record (fval :: fvals) ->
    m |- (PV_Record [fval]) ∈ (PT_Record fdecls) ->
    m |- (PV_Record fvals) ∈ t -> m |- v ∈ t
| HT_List (et : property_type) (elements : list property_value) :
    t = PT_List et ->
    v = PV_List elements ->
    Forall (fun e => m |- e ∈ et) elements -> m |- v ∈ t
| HT_Computed (s : string) :
    v = PV_Computed s -> m |- v ∈ t
where "m '|-' v '∈' t" := (has_typeR m t v).

Fixpoint same_type' (fuel : nat) (m : aadl_model) (t t' : property_type) : bool :=
  match fuel with
  | 0%nat => false
  | S n =>
    match t, t' with
    | aadlboolean, aadlboolean => true
    | aadlstring, aadlstring => true
    | aadlinteger, aadlinteger => true
    | aadlreal, aadldreal => true
    | PT_TypeRef qname1 as t1, PT_TypeRef qname2 as t2 =>
      if ps_qname_beq qname1 qname2 then true
      else
        match resolve_type m t1, resolve_type m t2 with
        | Some t1', Some t2' => same_type' n m t1' t2'
        | _, _ => false
        end
    | PT_TypeRef _ as t1, t2 =>
      match resolve_type m t1 with
      | Some t1' => same_type' n m t1' t2
      | _ => false
      end
    | t1, PT_TypeRef _ as t2 =>
      match resolve_type m t2 with
      | Some t2' => same_type' n m t1 t2'
      | _ => false
      end
    | _, _ => false
    end
  end.

Definition same_type := same_type' 10.

Fixpoint has_type' (fuel : nat) (m : aadl_model) (t : property_type) (v : property_value) : bool :=
  match print_id fuel with
  | 0%nat => false
  | S n =>
  match resolve_type m t with
  | Some t' =>
    match v with
    | PV_PropertyRef qname => match resolve_value m qname with
                             | Some t'' => same_type m t' t''
                             | _ => false
                             end
    | PV_Bool b => match t' with aadlboolean => true | _ => false end
    | PV_String s => match t' with aadlstring => true | _ => false end
    | PV_Enum i => in_enum i t'
    | PV_Unit i => in_units i t'
    | PV_Int _ => match t' with aadlinteger | PT_Number aadlinteger _ None => true | _ => false end
    | PV_Real _ => match t' with aadlreal | PT_Number aadlreal _ None => true | _ => false end
    | PV_IntU _ u =>
      match t' with
      | PT_Number aadlinteger _ (Some ut) => has_type' n m ut u
      | _ => false end
    | PV_RealU _ u =>
      match t' with
      | PT_Number aadlreal _ (Some ut) => has_type' n m ut u
      | _ => false end
    | PV_IntRange min max =>
      match t' with
      | PT_Range aadlinteger => has_type' n m aadlinteger min && has_type' n m aadlinteger max
      | _ => false
      end
    | PV_RealRange min max =>
      match t' with
      | PT_Range aadlreal => has_type' n m aadlreal min && has_type' n m aadlreal max
      | _ => false
      end
    | PV_IntRangeD min max Δ =>
      match t' with
      | PT_Range aadlinteger => has_type' n m aadlinteger min && has_type' n m aadlinteger max
                               && has_type' n m aadlinteger Δ
      | _ => false
      end
    | PV_RealRangeD min max Δ =>
      match t' with
      | PT_Range aadlreal => has_type' n m aadlreal min && has_type' n m aadlreal max
                            && has_type' n m aadlreal Δ
      | _ => false
      end
    | PV_Classifier => match t' with PT_Classifier => true | _ => false end
    | PV_ModelRef path => match t' with PT_Reference => true | _ => false end
    | PV_Record [] => match t' with PT_Record _ => true | _ => false end
    | PV_Record ((FieldVal vid fv as fval) :: fvals) =>
      match t' with
      | PT_Record (FieldDecl did ft :: fdecls) =>
        if identifier_beq did vid then
          if has_type' n m ft fv then
            has_type' n m t' (PV_Record fvals)
          else
            false
        else
          has_type' n m (PT_Record fdecls) (PV_Record [fval])
      | _ => false
                                            end
    | PV_List elements => match t' with
                         | PT_List et => fold_left
                                          (fun acc e => acc && (has_type' n m et e))
                                          elements true
                         | _ => false
                         end
    | PV_Computed _ => true
    end
  | _ => false
  end
  end.

Definition has_type := has_type' 20.

Notation "m '|=' v '∈' t" := (has_type m t v) (at level 60, v at next level).

Definition typecheck_ps_decl (m : aadl_model) (decl : property_set_declaration) : bool :=
  match decl with
  | PropertyConstantDecl _ t v => m |= v ∈ t
  | PropertyDecl _ t (Some v) _ => m |= v ∈ t
  | _ => true
  end.

Definition typecheck_model_unit (m : aadl_model) (mu : model_unit) : bool :=
  match mu with
  | PropertySet _ decls =>
    fold_left (fun acc decl => acc && typecheck_ps_decl m decl) decls true
  end.

Definition typecheck_model (m: aadl_model) : bool :=
  match m with
  | Model mus =>
    fold_left (fun acc mu => acc && typecheck_model_unit m mu) mus true
  end.

(* TODO :
   - check that the references are not cyclic
   - prove termination for resolution and typing fixpoints if there are no cycles
   - use efficient typing environment
   - add mapping from predeclared property name to predeclared property set name
   - how to report errors (cf. scalaz.Validation, cats.Validated)?
 *)
