  
Require Import List.
Import ListNotations. (* from List *)
Require Import Oqarina.core.identifiers.

Module AST.

    Inductive ComponentCategory_ast :=
        | COMPONENT_CATEGORY : identifier -> ComponentCategory_ast.

    Inductive DirectionType_ast :=
        | DIRECTION_TYPE : identifier -> DirectionType_ast.

    Inductive FeatureCategory_ast :=
        | FEATURE_CATEGORY : identifier -> FeatureCategory_ast.

    Inductive ID_ast :=
        | ID : list identifier -> ID_ast.

	Inductive ClassifierRef_ast :=
		| CLASSIFIER_REF : ID_ast -> identifier -> ClassifierRef_ast.

	Inductive DeclarativeRef_ast :=
		| DECLARATIVE_REF : ID_ast -> identifier -> identifier -> DeclarativeRef_ast.

	Inductive ImplRef_ast :=
		| IMPL_REF : ID_ast -> identifier -> identifier -> ImplRef_ast.

    Inductive ComponentInstance_ast :=
        | COMPONENT_INSTANCE : ComponentCategory_ast -> ClassifierRef_ast -> ID_ast -> DeclarativeRef_ast -> list Subclause_ast -> ComponentInstance_ast
	with FeatureInstance_ast :=
		| FEATURE_INSTANCE : DirectionType_ast -> FeatureCategory_ast  -> ID_ast -> DeclarativeRef_ast -> FeatureInstance_ast
	with Subclause_ast :=
		| COMPONENT : ComponentInstance_ast -> Subclause_ast
		| FEATURE : FeatureInstance_ast -> Subclause_ast.

    Inductive node :=
        | ROOT_SYSTEM : ComponentCategory_ast -> ID_ast -> ImplRef_ast  -> list Subclause_ast -> node.


End AST.



From Coq.Lists Require List.
From Coq.PArith Require Import BinPos.
From Coq.NArith Require Import BinNat.
From MenhirLib Require Main.
From MenhirLib Require Version.
Import List.ListNotations.

Definition version_check : unit := MenhirLib.Version.require_unreleased.

Unset Elimination Schemes.

Inductive token : Type :=
| RIGHT_BRACE : unit%type -> token
| NUM :       (nat)%type -> token
| LEFT_BRACE : unit%type -> token
| ID :       (string)%type -> token
| FEATURE_CATEGORY :       (string)%type -> token
| EOF : unit%type -> token
| DOT : unit%type -> token
| DIRECTION_TYPE :       (string)%type -> token
| COMPONENT_CATEGORY :       (string)%type -> token
| COLONx2 : unit%type -> token
| COLON : unit%type -> token.

Module Import Gram <: MenhirLib.Grammar.T.

Local Obligation Tactic := let x := fresh in intro x; case x; reflexivity.

Inductive terminal' : Set :=
| COLON't
| COLONx2't
| COMPONENT_CATEGORY't
| DIRECTION_TYPE't
| DOT't
| EOF't
| FEATURE_CATEGORY't
| ID't
| LEFT_BRACE't
| NUM't
| RIGHT_BRACE't.
Definition terminal := terminal'.

Program Instance terminalNum : MenhirLib.Alphabet.Numbered terminal :=
  { inj := fun x => match x return _ with
    | COLON't => 1%positive
    | COLONx2't => 2%positive
    | COMPONENT_CATEGORY't => 3%positive
    | DIRECTION_TYPE't => 4%positive
    | DOT't => 5%positive
    | EOF't => 6%positive
    | FEATURE_CATEGORY't => 7%positive
    | ID't => 8%positive
    | LEFT_BRACE't => 9%positive
    | NUM't => 10%positive
    | RIGHT_BRACE't => 11%positive
    end;
    surj := (fun n => match n return _ with
    | 1%positive => COLON't
    | 2%positive => COLONx2't
    | 3%positive => COMPONENT_CATEGORY't
    | 4%positive => DIRECTION_TYPE't
    | 5%positive => DOT't
    | 6%positive => EOF't
    | 7%positive => FEATURE_CATEGORY't
    | 8%positive => ID't
    | 9%positive => LEFT_BRACE't
    | 10%positive => NUM't
    | 11%positive => RIGHT_BRACE't
    | _ => COLON't
    end)%Z;
    inj_bound := 11%positive }.
Instance TerminalAlph : MenhirLib.Alphabet.Alphabet terminal := _.

Inductive nonterminal' : Set :=
| main'nt
| p_ClassifierRef'nt
| p_ComponentCategory'nt
| p_ComponentInstance'nt
| p_DeclarativeRef'nt
| p_DirectionType'nt
| p_FeatureCategory'nt
| p_FeatureInstance'nt
| p_ImplRef'nt
| p_SystemInstance'nt
| p_id'nt
| p_idlist'nt
| p_idlist_inner'nt
| p_main'nt
| p_subclause_element'nt
| p_subclause_list'nt
| p_subclause_list_inner'nt.
Definition nonterminal := nonterminal'.

Program Instance nonterminalNum : MenhirLib.Alphabet.Numbered nonterminal :=
  { inj := fun x => match x return _ with
    | main'nt => 1%positive
    | p_ClassifierRef'nt => 2%positive
    | p_ComponentCategory'nt => 3%positive
    | p_ComponentInstance'nt => 4%positive
    | p_DeclarativeRef'nt => 5%positive
    | p_DirectionType'nt => 6%positive
    | p_FeatureCategory'nt => 7%positive
    | p_FeatureInstance'nt => 8%positive
    | p_ImplRef'nt => 9%positive
    | p_SystemInstance'nt => 10%positive
    | p_id'nt => 11%positive
    | p_idlist'nt => 12%positive
    | p_idlist_inner'nt => 13%positive
    | p_main'nt => 14%positive
    | p_subclause_element'nt => 15%positive
    | p_subclause_list'nt => 16%positive
    | p_subclause_list_inner'nt => 17%positive
    end;
    surj := (fun n => match n return _ with
    | 1%positive => main'nt
    | 2%positive => p_ClassifierRef'nt
    | 3%positive => p_ComponentCategory'nt
    | 4%positive => p_ComponentInstance'nt
    | 5%positive => p_DeclarativeRef'nt
    | 6%positive => p_DirectionType'nt
    | 7%positive => p_FeatureCategory'nt
    | 8%positive => p_FeatureInstance'nt
    | 9%positive => p_ImplRef'nt
    | 10%positive => p_SystemInstance'nt
    | 11%positive => p_id'nt
    | 12%positive => p_idlist'nt
    | 13%positive => p_idlist_inner'nt
    | 14%positive => p_main'nt
    | 15%positive => p_subclause_element'nt
    | 16%positive => p_subclause_list'nt
    | 17%positive => p_subclause_list_inner'nt
    | _ => main'nt
    end)%Z;
    inj_bound := 17%positive }.
Instance NonTerminalAlph : MenhirLib.Alphabet.Alphabet nonterminal := _.

Include MenhirLib.Grammar.Symbol.

Definition terminal_semantic_type (t:terminal) : Type:=
  match t with
  | RIGHT_BRACE't => unit%type
  | NUM't =>       (nat)%type
  | LEFT_BRACE't => unit%type
  | ID't =>       (string)%type
  | FEATURE_CATEGORY't =>       (string)%type
  | EOF't => unit%type
  | DOT't => unit%type
  | DIRECTION_TYPE't =>       (string)%type
  | COMPONENT_CATEGORY't =>       (string)%type
  | COLONx2't => unit%type
  | COLON't => unit%type
  end.

Definition nonterminal_semantic_type (nt:nonterminal) : Type:=
  match nt with
  | p_subclause_list_inner'nt =>      (list AST.Subclause_ast)%type
  | p_subclause_list'nt =>      (list AST.Subclause_ast)%type
  | p_subclause_element'nt =>      (AST.Subclause_ast)%type
  | p_main'nt =>      (AST.node)%type
  | p_idlist_inner'nt =>      (list identifier)%type
  | p_idlist'nt =>      (AST.ID_ast)%type
  | p_id'nt =>      (AST.ID_ast)%type
  | p_SystemInstance'nt =>      (AST.node)%type
  | p_ImplRef'nt =>      (AST.ImplRef_ast)%type
  | p_FeatureInstance'nt =>      (AST.FeatureInstance_ast)%type
  | p_FeatureCategory'nt =>      (AST.FeatureCategory_ast)%type
  | p_DirectionType'nt =>      (AST.DirectionType_ast)%type
  | p_DeclarativeRef'nt =>      (AST.DeclarativeRef_ast)%type
  | p_ComponentInstance'nt =>      (AST.ComponentInstance_ast)%type
  | p_ComponentCategory'nt =>      (AST.ComponentCategory_ast)%type
  | p_ClassifierRef'nt =>      (AST.ClassifierRef_ast)%type
  | main'nt =>       (AST.node)%type
  end.

Definition symbol_semantic_type (s:symbol) : Type:=
  match s with
  | T t => terminal_semantic_type t
  | NT nt => nonterminal_semantic_type nt
  end.

Definition token := token.

Definition token_term (tok : token) : terminal :=
  match tok with
  | RIGHT_BRACE _ => RIGHT_BRACE't
  | NUM _ => NUM't
  | LEFT_BRACE _ => LEFT_BRACE't
  | ID _ => ID't
  | FEATURE_CATEGORY _ => FEATURE_CATEGORY't
  | EOF _ => EOF't
  | DOT _ => DOT't
  | DIRECTION_TYPE _ => DIRECTION_TYPE't
  | COMPONENT_CATEGORY _ => COMPONENT_CATEGORY't
  | COLONx2 _ => COLONx2't
  | COLON _ => COLON't
  end.

Definition token_sem (tok : token) : symbol_semantic_type (T (token_term tok)) :=
  match tok with
  | RIGHT_BRACE x => x
  | NUM x => x
  | LEFT_BRACE x => x
  | ID x => x
  | FEATURE_CATEGORY x => x
  | EOF x => x
  | DOT x => x
  | DIRECTION_TYPE x => x
  | COMPONENT_CATEGORY x => x
  | COLONx2 x => x
  | COLON x => x
  end.

Inductive production' : Set :=
| Prod'p_subclause_list_inner'1
| Prod'p_subclause_list_inner'0
| Prod'p_subclause_list'0
| Prod'p_subclause_element'1
| Prod'p_subclause_element'0
| Prod'p_main'0
| Prod'p_idlist_inner'1
| Prod'p_idlist_inner'0
| Prod'p_idlist'0
| Prod'p_id'0
| Prod'p_SystemInstance'0
| Prod'p_ImplRef'0
| Prod'p_FeatureInstance'0
| Prod'p_FeatureCategory'0
| Prod'p_DirectionType'0
| Prod'p_DeclarativeRef'1
| Prod'p_DeclarativeRef'0
| Prod'p_ComponentInstance'0
| Prod'p_ComponentCategory'0
| Prod'p_ClassifierRef'1
| Prod'p_ClassifierRef'0
| Prod'main'0.
Definition production := production'.

Program Instance productionNum : MenhirLib.Alphabet.Numbered production :=
  { inj := fun x => match x return _ with
    | Prod'p_subclause_list_inner'1 => 1%positive
    | Prod'p_subclause_list_inner'0 => 2%positive
    | Prod'p_subclause_list'0 => 3%positive
    | Prod'p_subclause_element'1 => 4%positive
    | Prod'p_subclause_element'0 => 5%positive
    | Prod'p_main'0 => 6%positive
    | Prod'p_idlist_inner'1 => 7%positive
    | Prod'p_idlist_inner'0 => 8%positive
    | Prod'p_idlist'0 => 9%positive
    | Prod'p_id'0 => 10%positive
    | Prod'p_SystemInstance'0 => 11%positive
    | Prod'p_ImplRef'0 => 12%positive
    | Prod'p_FeatureInstance'0 => 13%positive
    | Prod'p_FeatureCategory'0 => 14%positive
    | Prod'p_DirectionType'0 => 15%positive
    | Prod'p_DeclarativeRef'1 => 16%positive
    | Prod'p_DeclarativeRef'0 => 17%positive
    | Prod'p_ComponentInstance'0 => 18%positive
    | Prod'p_ComponentCategory'0 => 19%positive
    | Prod'p_ClassifierRef'1 => 20%positive
    | Prod'p_ClassifierRef'0 => 21%positive
    | Prod'main'0 => 22%positive
    end;
    surj := (fun n => match n return _ with
    | 1%positive => Prod'p_subclause_list_inner'1
    | 2%positive => Prod'p_subclause_list_inner'0
    | 3%positive => Prod'p_subclause_list'0
    | 4%positive => Prod'p_subclause_element'1
    | 5%positive => Prod'p_subclause_element'0
    | 6%positive => Prod'p_main'0
    | 7%positive => Prod'p_idlist_inner'1
    | 8%positive => Prod'p_idlist_inner'0
    | 9%positive => Prod'p_idlist'0
    | 10%positive => Prod'p_id'0
    | 11%positive => Prod'p_SystemInstance'0
    | 12%positive => Prod'p_ImplRef'0
    | 13%positive => Prod'p_FeatureInstance'0
    | 14%positive => Prod'p_FeatureCategory'0
    | 15%positive => Prod'p_DirectionType'0
    | 16%positive => Prod'p_DeclarativeRef'1
    | 17%positive => Prod'p_DeclarativeRef'0
    | 18%positive => Prod'p_ComponentInstance'0
    | 19%positive => Prod'p_ComponentCategory'0
    | 20%positive => Prod'p_ClassifierRef'1
    | 21%positive => Prod'p_ClassifierRef'0
    | 22%positive => Prod'main'0
    | _ => Prod'p_subclause_list_inner'1
    end)%Z;
    inj_bound := 22%positive }.
Instance ProductionAlph : MenhirLib.Alphabet.Alphabet production := _.

Definition prod_contents (p:production) :
  { p:nonterminal * list symbol &
    MenhirLib.Grammar.arrows_right
      (symbol_semantic_type (NT (fst p)))
      (List.map symbol_semantic_type (snd p)) }
 :=
  let box := existT (fun p =>
    MenhirLib.Grammar.arrows_right
      (symbol_semantic_type (NT (fst p)))
      (List.map symbol_semantic_type (snd p)) )
  in
  match p with
  | Prod'main'0 => box
    (main'nt, [T EOF't; NT p_main'nt]%list)
    (fun _2 _1 =>
                       ( _1 )
)
  | Prod'p_ClassifierRef'0 => box
    (p_ClassifierRef'nt, [T ID't; T DOT't; NT p_idlist'nt]%list)
    (fun _3 _2 _1 =>
                  ( AST.CLASSIFIER_REF _1 (Id _3) )
)
  | Prod'p_ClassifierRef'1 => box
    (p_ClassifierRef'nt, [NT p_idlist'nt]%list)
    (fun _1 =>
                  ( AST.CLASSIFIER_REF _1 empty_identifier )
)
  | Prod'p_ComponentCategory'0 => box
    (p_ComponentCategory'nt, [T COMPONENT_CATEGORY't]%list)
    (fun _1 =>
                     ( AST.COMPONENT_CATEGORY (Id _1) )
)
  | Prod'p_ComponentInstance'0 => box
    (p_ComponentInstance'nt, [NT p_subclause_list'nt; NT p_DeclarativeRef'nt; T COLON't; NT p_id'nt; NT p_ClassifierRef'nt; NT p_ComponentCategory'nt]%list)
    (fun _6 _5 _4 _3 _2 _1 =>
                                                                                    ( AST.COMPONENT_INSTANCE _1 _2 _3 _5 _6 )
)
  | Prod'p_DeclarativeRef'0 => box
    (p_DeclarativeRef'nt, [T ID't; T COLON't; T ID't; T DOT't; NT p_idlist'nt]%list)
    (fun _5 _4 _3 _2 _1 =>
                           ( AST.DECLARATIVE_REF _1 (Id _3) (Id _5) )
)
  | Prod'p_DeclarativeRef'1 => box
    (p_DeclarativeRef'nt, [T ID't; T COLON't; NT p_idlist'nt]%list)
    (fun _3 _2 _1 =>
                           ( AST.DECLARATIVE_REF _1 (Id _3) empty_identifier )
)
  | Prod'p_DirectionType'0 => box
    (p_DirectionType'nt, [T DIRECTION_TYPE't]%list)
    (fun _1 =>
                 ( AST.DIRECTION_TYPE (Id _1) )
)
  | Prod'p_FeatureCategory'0 => box
    (p_FeatureCategory'nt, [T FEATURE_CATEGORY't]%list)
    (fun _1 =>
                   ( AST.FEATURE_CATEGORY(Id _1) )
)
  | Prod'p_FeatureInstance'0 => box
    (p_FeatureInstance'nt, [NT p_DeclarativeRef'nt; T COLON't; NT p_id'nt; NT p_FeatureCategory'nt; NT p_DirectionType'nt]%list)
    (fun _5 _4 _3 _2 _1 =>
                                                                ( AST.FEATURE_INSTANCE _1 _2 _3 _5 )
)
  | Prod'p_ImplRef'0 => box
    (p_ImplRef'nt, [T ID't; T DOT't; NT p_idlist'nt]%list)
    (fun _3 _2 _1 =>
                  ( AST.IMPL_REF _1 (Id _3) empty_identifier )
)
  | Prod'p_SystemInstance'0 => box
    (p_SystemInstance'nt, [NT p_subclause_list'nt; NT p_ImplRef'nt; T COLON't; NT p_id'nt; NT p_ComponentCategory'nt]%list)
    (fun _5 _4 _3 _2 _1 =>
                                                            ( AST.ROOT_SYSTEM _1 _2 _4 _5 )
)
  | Prod'p_id'0 => box
    (p_id'nt, [T ID't]%list)
    (fun _1 =>
     ( AST.ID [ Id _1 ] )
)
  | Prod'p_idlist'0 => box
    (p_idlist'nt, [NT p_idlist_inner'nt; T ID't]%list)
    (fun _2 _1 =>
                    ( AST.ID ([ Id _1 ] ++ _2) )
)
  | Prod'p_idlist_inner'0 => box
    (p_idlist_inner'nt, [T ID't; T COLONx2't]%list)
    (fun _2 _1 =>
                            ( [Id _2] )
)
  | Prod'p_idlist_inner'1 => box
    (p_idlist_inner'nt, [NT p_idlist_inner'nt; T ID't; T COLONx2't]%list)
    (fun _3 _2 _1 =>
                            ( [ Id _2 ] ++ _3)
)
  | Prod'p_main'0 => box
    (p_main'nt, [NT p_SystemInstance'nt]%list)
    (fun _1 =>
                   ( _1 )
)
  | Prod'p_subclause_element'0 => box
    (p_subclause_element'nt, [NT p_ComponentInstance'nt]%list)
    (fun _1 =>
                      ( AST.COMPONENT _1 )
)
  | Prod'p_subclause_element'1 => box
    (p_subclause_element'nt, [NT p_FeatureInstance'nt]%list)
    (fun _1 =>
                      ( AST.FEATURE _1 )
)
  | Prod'p_subclause_list'0 => box
    (p_subclause_list'nt, [NT p_subclause_list_inner'nt; T LEFT_BRACE't]%list)
    (fun _2 _1 =>
                                    ( _2 )
)
  | Prod'p_subclause_list_inner'0 => box
    (p_subclause_list_inner'nt, [T RIGHT_BRACE't]%list)
    (fun _1 =>
              ( [ ] )
)
  | Prod'p_subclause_list_inner'1 => box
    (p_subclause_list_inner'nt, [NT p_subclause_list_inner'nt; NT p_subclause_element'nt]%list)
    (fun _2 _1 =>
                                             ( _1 :: _2 )
)
  end.

Definition prod_lhs (p:production) :=
  fst (projT1 (prod_contents p)).
Definition prod_rhs_rev (p:production) :=
  snd (projT1 (prod_contents p)).
Definition prod_action (p:production) :=
  projT2 (prod_contents p).

Include MenhirLib.Grammar.Defs.

End Gram.

Module Aut <: MenhirLib.Automaton.T.

Local Obligation Tactic := let x := fresh in intro x; case x; reflexivity.

Module Gram := Gram.
Module GramDefs := Gram.

Definition nullable_nterm (nt:nonterminal) : bool :=
  match nt with
  | p_subclause_list_inner'nt => false
  | p_subclause_list'nt => false
  | p_subclause_element'nt => false
  | p_main'nt => false
  | p_idlist_inner'nt => false
  | p_idlist'nt => false
  | p_id'nt => false
  | p_SystemInstance'nt => false
  | p_ImplRef'nt => false
  | p_FeatureInstance'nt => false
  | p_FeatureCategory'nt => false
  | p_DirectionType'nt => false
  | p_DeclarativeRef'nt => false
  | p_ComponentInstance'nt => false
  | p_ComponentCategory'nt => false
  | p_ClassifierRef'nt => false
  | main'nt => false
  end.

Definition first_nterm (nt:nonterminal) : list terminal :=
  match nt with
  | p_subclause_list_inner'nt => [RIGHT_BRACE't; DIRECTION_TYPE't; COMPONENT_CATEGORY't]%list
  | p_subclause_list'nt => [LEFT_BRACE't]%list
  | p_subclause_element'nt => [DIRECTION_TYPE't; COMPONENT_CATEGORY't]%list
  | p_main'nt => [COMPONENT_CATEGORY't]%list
  | p_idlist_inner'nt => [COLONx2't]%list
  | p_idlist'nt => [ID't]%list
  | p_id'nt => [ID't]%list
  | p_SystemInstance'nt => [COMPONENT_CATEGORY't]%list
  | p_ImplRef'nt => [ID't]%list
  | p_FeatureInstance'nt => [DIRECTION_TYPE't]%list
  | p_FeatureCategory'nt => [FEATURE_CATEGORY't]%list
  | p_DirectionType'nt => [DIRECTION_TYPE't]%list
  | p_DeclarativeRef'nt => [ID't]%list
  | p_ComponentInstance'nt => [COMPONENT_CATEGORY't]%list
  | p_ComponentCategory'nt => [COMPONENT_CATEGORY't]%list
  | p_ClassifierRef'nt => [ID't]%list
  | main'nt => [COMPONENT_CATEGORY't]%list
  end.

Inductive noninitstate' : Set :=
| Nis'48
| Nis'47
| Nis'46
| Nis'45
| Nis'44
| Nis'43
| Nis'42
| Nis'41
| Nis'40
| Nis'39
| Nis'38
| Nis'37
| Nis'36
| Nis'35
| Nis'34
| Nis'33
| Nis'32
| Nis'31
| Nis'30
| Nis'29
| Nis'28
| Nis'27
| Nis'26
| Nis'25
| Nis'24
| Nis'23
| Nis'22
| Nis'21
| Nis'20
| Nis'19
| Nis'18
| Nis'17
| Nis'16
| Nis'15
| Nis'14
| Nis'13
| Nis'12
| Nis'11
| Nis'10
| Nis'9
| Nis'8
| Nis'7
| Nis'6
| Nis'5
| Nis'4
| Nis'3
| Nis'2
| Nis'1.
Definition noninitstate := noninitstate'.

Program Instance noninitstateNum : MenhirLib.Alphabet.Numbered noninitstate :=
  { inj := fun x => match x return _ with
    | Nis'48 => 1%positive
    | Nis'47 => 2%positive
    | Nis'46 => 3%positive
    | Nis'45 => 4%positive
    | Nis'44 => 5%positive
    | Nis'43 => 6%positive
    | Nis'42 => 7%positive
    | Nis'41 => 8%positive
    | Nis'40 => 9%positive
    | Nis'39 => 10%positive
    | Nis'38 => 11%positive
    | Nis'37 => 12%positive
    | Nis'36 => 13%positive
    | Nis'35 => 14%positive
    | Nis'34 => 15%positive
    | Nis'33 => 16%positive
    | Nis'32 => 17%positive
    | Nis'31 => 18%positive
    | Nis'30 => 19%positive
    | Nis'29 => 20%positive
    | Nis'28 => 21%positive
    | Nis'27 => 22%positive
    | Nis'26 => 23%positive
    | Nis'25 => 24%positive
    | Nis'24 => 25%positive
    | Nis'23 => 26%positive
    | Nis'22 => 27%positive
    | Nis'21 => 28%positive
    | Nis'20 => 29%positive
    | Nis'19 => 30%positive
    | Nis'18 => 31%positive
    | Nis'17 => 32%positive
    | Nis'16 => 33%positive
    | Nis'15 => 34%positive
    | Nis'14 => 35%positive
    | Nis'13 => 36%positive
    | Nis'12 => 37%positive
    | Nis'11 => 38%positive
    | Nis'10 => 39%positive
    | Nis'9 => 40%positive
    | Nis'8 => 41%positive
    | Nis'7 => 42%positive
    | Nis'6 => 43%positive
    | Nis'5 => 44%positive
    | Nis'4 => 45%positive
    | Nis'3 => 46%positive
    | Nis'2 => 47%positive
    | Nis'1 => 48%positive
    end;
    surj := (fun n => match n return _ with
    | 1%positive => Nis'48
    | 2%positive => Nis'47
    | 3%positive => Nis'46
    | 4%positive => Nis'45
    | 5%positive => Nis'44
    | 6%positive => Nis'43
    | 7%positive => Nis'42
    | 8%positive => Nis'41
    | 9%positive => Nis'40
    | 10%positive => Nis'39
    | 11%positive => Nis'38
    | 12%positive => Nis'37
    | 13%positive => Nis'36
    | 14%positive => Nis'35
    | 15%positive => Nis'34
    | 16%positive => Nis'33
    | 17%positive => Nis'32
    | 18%positive => Nis'31
    | 19%positive => Nis'30
    | 20%positive => Nis'29
    | 21%positive => Nis'28
    | 22%positive => Nis'27
    | 23%positive => Nis'26
    | 24%positive => Nis'25
    | 25%positive => Nis'24
    | 26%positive => Nis'23
    | 27%positive => Nis'22
    | 28%positive => Nis'21
    | 29%positive => Nis'20
    | 30%positive => Nis'19
    | 31%positive => Nis'18
    | 32%positive => Nis'17
    | 33%positive => Nis'16
    | 34%positive => Nis'15
    | 35%positive => Nis'14
    | 36%positive => Nis'13
    | 37%positive => Nis'12
    | 38%positive => Nis'11
    | 39%positive => Nis'10
    | 40%positive => Nis'9
    | 41%positive => Nis'8
    | 42%positive => Nis'7
    | 43%positive => Nis'6
    | 44%positive => Nis'5
    | 45%positive => Nis'4
    | 46%positive => Nis'3
    | 47%positive => Nis'2
    | 48%positive => Nis'1
    | _ => Nis'48
    end)%Z;
    inj_bound := 48%positive }.
Instance NonInitStateAlph : MenhirLib.Alphabet.Alphabet noninitstate := _.

Definition last_symb_of_non_init_state (noninitstate:noninitstate) : symbol :=
  match noninitstate with
  | Nis'1 => T COMPONENT_CATEGORY't
  | Nis'2 => NT p_main'nt
  | Nis'3 => T EOF't
  | Nis'4 => NT p_SystemInstance'nt
  | Nis'5 => NT p_ComponentCategory'nt
  | Nis'6 => T ID't
  | Nis'7 => NT p_id'nt
  | Nis'8 => T COLON't
  | Nis'9 => T ID't
  | Nis'10 => T COLONx2't
  | Nis'11 => T ID't
  | Nis'12 => NT p_idlist_inner'nt
  | Nis'13 => NT p_idlist_inner'nt
  | Nis'14 => NT p_idlist'nt
  | Nis'15 => T DOT't
  | Nis'16 => T ID't
  | Nis'17 => NT p_ImplRef'nt
  | Nis'18 => T LEFT_BRACE't
  | Nis'19 => T RIGHT_BRACE't
  | Nis'20 => T DIRECTION_TYPE't
  | Nis'21 => NT p_subclause_list_inner'nt
  | Nis'22 => NT p_subclause_element'nt
  | Nis'23 => NT p_subclause_list_inner'nt
  | Nis'24 => NT p_FeatureInstance'nt
  | Nis'25 => NT p_DirectionType'nt
  | Nis'26 => T FEATURE_CATEGORY't
  | Nis'27 => NT p_FeatureCategory'nt
  | Nis'28 => NT p_id'nt
  | Nis'29 => T COLON't
  | Nis'30 => NT p_idlist'nt
  | Nis'31 => T DOT't
  | Nis'32 => T ID't
  | Nis'33 => T COLON't
  | Nis'34 => T ID't
  | Nis'35 => T COLON't
  | Nis'36 => T ID't
  | Nis'37 => NT p_DeclarativeRef'nt
  | Nis'38 => NT p_ComponentInstance'nt
  | Nis'39 => NT p_ComponentCategory'nt
  | Nis'40 => NT p_idlist'nt
  | Nis'41 => T DOT't
  | Nis'42 => T ID't
  | Nis'43 => NT p_ClassifierRef'nt
  | Nis'44 => NT p_id'nt
  | Nis'45 => T COLON't
  | Nis'46 => NT p_DeclarativeRef'nt
  | Nis'47 => NT p_subclause_list'nt
  | Nis'48 => NT p_subclause_list'nt
  end.

Inductive initstate' : Set :=
| Init'0.
Definition initstate := initstate'.

Program Instance initstateNum : MenhirLib.Alphabet.Numbered initstate :=
  { inj := fun x => match x return _ with
    | Init'0 => 1%positive
    end;
    surj := (fun n => match n return _ with
    | 1%positive => Init'0
    | _ => Init'0
    end)%Z;
    inj_bound := 1%positive }.
Instance InitStateAlph : MenhirLib.Alphabet.Alphabet initstate := _.

Include MenhirLib.Automaton.Types.

Definition start_nt (init:initstate) : nonterminal :=
  match init with
  | Init'0 => main'nt
  end.

Definition action_table (state:state) : action :=
  match state with
  | Init Init'0 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | COMPONENT_CATEGORY't => Shift_act Nis'1 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'1 => Default_reduce_act Prod'p_ComponentCategory'0
  | Ninit Nis'2 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | EOF't => Shift_act Nis'3 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'3 => Default_reduce_act Prod'main'0
  | Ninit Nis'4 => Default_reduce_act Prod'p_main'0
  | Ninit Nis'5 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | ID't => Shift_act Nis'6 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'6 => Default_reduce_act Prod'p_id'0
  | Ninit Nis'7 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | COLON't => Shift_act Nis'8 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'8 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | ID't => Shift_act Nis'9 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'9 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | COLONx2't => Shift_act Nis'10 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'10 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | ID't => Shift_act Nis'11 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'11 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | ID't => Reduce_act Prod'p_idlist_inner'0
    | DOT't => Reduce_act Prod'p_idlist_inner'0
    | COLONx2't => Shift_act Nis'10 (eq_refl _)
    | COLON't => Reduce_act Prod'p_idlist_inner'0
    | _ => Fail_act
    end)
  | Ninit Nis'12 => Default_reduce_act Prod'p_idlist_inner'1
  | Ninit Nis'13 => Default_reduce_act Prod'p_idlist'0
  | Ninit Nis'14 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | DOT't => Shift_act Nis'15 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'15 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | ID't => Shift_act Nis'16 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'16 => Default_reduce_act Prod'p_ImplRef'0
  | Ninit Nis'17 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | LEFT_BRACE't => Shift_act Nis'18 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'18 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | RIGHT_BRACE't => Shift_act Nis'19 (eq_refl _)
    | DIRECTION_TYPE't => Shift_act Nis'20 (eq_refl _)
    | COMPONENT_CATEGORY't => Shift_act Nis'1 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'19 => Default_reduce_act Prod'p_subclause_list_inner'0
  | Ninit Nis'20 => Default_reduce_act Prod'p_DirectionType'0
  | Ninit Nis'21 => Default_reduce_act Prod'p_subclause_list'0
  | Ninit Nis'22 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | RIGHT_BRACE't => Shift_act Nis'19 (eq_refl _)
    | DIRECTION_TYPE't => Shift_act Nis'20 (eq_refl _)
    | COMPONENT_CATEGORY't => Shift_act Nis'1 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'23 => Default_reduce_act Prod'p_subclause_list_inner'1
  | Ninit Nis'24 => Default_reduce_act Prod'p_subclause_element'1
  | Ninit Nis'25 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | FEATURE_CATEGORY't => Shift_act Nis'26 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'26 => Default_reduce_act Prod'p_FeatureCategory'0
  | Ninit Nis'27 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | ID't => Shift_act Nis'6 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'28 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | COLON't => Shift_act Nis'29 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'29 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | ID't => Shift_act Nis'9 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'30 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | DOT't => Shift_act Nis'31 (eq_refl _)
    | COLON't => Shift_act Nis'35 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'31 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | ID't => Shift_act Nis'32 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'32 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | COLON't => Shift_act Nis'33 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'33 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | ID't => Shift_act Nis'34 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'34 => Default_reduce_act Prod'p_DeclarativeRef'0
  | Ninit Nis'35 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | ID't => Shift_act Nis'36 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'36 => Default_reduce_act Prod'p_DeclarativeRef'1
  | Ninit Nis'37 => Default_reduce_act Prod'p_FeatureInstance'0
  | Ninit Nis'38 => Default_reduce_act Prod'p_subclause_element'0
  | Ninit Nis'39 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | ID't => Shift_act Nis'9 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'40 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | ID't => Reduce_act Prod'p_ClassifierRef'1
    | DOT't => Shift_act Nis'41 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'41 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | ID't => Shift_act Nis'42 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'42 => Default_reduce_act Prod'p_ClassifierRef'0
  | Ninit Nis'43 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | ID't => Shift_act Nis'6 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'44 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | COLON't => Shift_act Nis'45 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'45 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | ID't => Shift_act Nis'9 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'46 => Lookahead_act (fun terminal:terminal =>
    match terminal return lookahead_action terminal with
    | LEFT_BRACE't => Shift_act Nis'18 (eq_refl _)
    | _ => Fail_act
    end)
  | Ninit Nis'47 => Default_reduce_act Prod'p_ComponentInstance'0
  | Ninit Nis'48 => Default_reduce_act Prod'p_SystemInstance'0
  end.

Definition goto_table (state:state) (nt:nonterminal) :=
  match state, nt return option { s:noninitstate | NT nt = last_symb_of_non_init_state s } with
  | Init Init'0, p_main'nt => Some (exist _ Nis'2 (eq_refl _))
  | Init Init'0, p_SystemInstance'nt => Some (exist _ Nis'4 (eq_refl _))
  | Init Init'0, p_ComponentCategory'nt => Some (exist _ Nis'5 (eq_refl _))
  | Init Init'0, main'nt => None  | Ninit Nis'5, p_id'nt => Some (exist _ Nis'7 (eq_refl _))
  | Ninit Nis'8, p_idlist'nt => Some (exist _ Nis'14 (eq_refl _))
  | Ninit Nis'8, p_ImplRef'nt => Some (exist _ Nis'17 (eq_refl _))
  | Ninit Nis'9, p_idlist_inner'nt => Some (exist _ Nis'13 (eq_refl _))
  | Ninit Nis'11, p_idlist_inner'nt => Some (exist _ Nis'12 (eq_refl _))
  | Ninit Nis'17, p_subclause_list'nt => Some (exist _ Nis'48 (eq_refl _))
  | Ninit Nis'18, p_subclause_list_inner'nt => Some (exist _ Nis'21 (eq_refl _))
  | Ninit Nis'18, p_subclause_element'nt => Some (exist _ Nis'22 (eq_refl _))
  | Ninit Nis'18, p_FeatureInstance'nt => Some (exist _ Nis'24 (eq_refl _))
  | Ninit Nis'18, p_DirectionType'nt => Some (exist _ Nis'25 (eq_refl _))
  | Ninit Nis'18, p_ComponentInstance'nt => Some (exist _ Nis'38 (eq_refl _))
  | Ninit Nis'18, p_ComponentCategory'nt => Some (exist _ Nis'39 (eq_refl _))
  | Ninit Nis'22, p_subclause_list_inner'nt => Some (exist _ Nis'23 (eq_refl _))
  | Ninit Nis'22, p_subclause_element'nt => Some (exist _ Nis'22 (eq_refl _))
  | Ninit Nis'22, p_FeatureInstance'nt => Some (exist _ Nis'24 (eq_refl _))
  | Ninit Nis'22, p_DirectionType'nt => Some (exist _ Nis'25 (eq_refl _))
  | Ninit Nis'22, p_ComponentInstance'nt => Some (exist _ Nis'38 (eq_refl _))
  | Ninit Nis'22, p_ComponentCategory'nt => Some (exist _ Nis'39 (eq_refl _))
  | Ninit Nis'25, p_FeatureCategory'nt => Some (exist _ Nis'27 (eq_refl _))
  | Ninit Nis'27, p_id'nt => Some (exist _ Nis'28 (eq_refl _))
  | Ninit Nis'29, p_idlist'nt => Some (exist _ Nis'30 (eq_refl _))
  | Ninit Nis'29, p_DeclarativeRef'nt => Some (exist _ Nis'37 (eq_refl _))
  | Ninit Nis'39, p_idlist'nt => Some (exist _ Nis'40 (eq_refl _))
  | Ninit Nis'39, p_ClassifierRef'nt => Some (exist _ Nis'43 (eq_refl _))
  | Ninit Nis'43, p_id'nt => Some (exist _ Nis'44 (eq_refl _))
  | Ninit Nis'45, p_idlist'nt => Some (exist _ Nis'30 (eq_refl _))
  | Ninit Nis'45, p_DeclarativeRef'nt => Some (exist _ Nis'46 (eq_refl _))
  | Ninit Nis'46, p_subclause_list'nt => Some (exist _ Nis'47 (eq_refl _))
  | _, _ => None
  end.

Definition past_symb_of_non_init_state (noninitstate:noninitstate) : list symbol :=
  match noninitstate with
  | Nis'1 => []%list
  | Nis'2 => []%list
  | Nis'3 => [NT p_main'nt]%list
  | Nis'4 => []%list
  | Nis'5 => []%list
  | Nis'6 => []%list
  | Nis'7 => [NT p_ComponentCategory'nt]%list
  | Nis'8 => [NT p_id'nt; NT p_ComponentCategory'nt]%list
  | Nis'9 => []%list
  | Nis'10 => []%list
  | Nis'11 => [T COLONx2't]%list
  | Nis'12 => [T ID't; T COLONx2't]%list
  | Nis'13 => [T ID't]%list
  | Nis'14 => []%list
  | Nis'15 => [NT p_idlist'nt]%list
  | Nis'16 => [T DOT't; NT p_idlist'nt]%list
  | Nis'17 => [T COLON't; NT p_id'nt; NT p_ComponentCategory'nt]%list
  | Nis'18 => []%list
  | Nis'19 => []%list
  | Nis'20 => []%list
  | Nis'21 => [T LEFT_BRACE't]%list
  | Nis'22 => []%list
  | Nis'23 => [NT p_subclause_element'nt]%list
  | Nis'24 => []%list
  | Nis'25 => []%list
  | Nis'26 => []%list
  | Nis'27 => [NT p_DirectionType'nt]%list
  | Nis'28 => [NT p_FeatureCategory'nt; NT p_DirectionType'nt]%list
  | Nis'29 => [NT p_id'nt; NT p_FeatureCategory'nt; NT p_DirectionType'nt]%list
  | Nis'30 => []%list
  | Nis'31 => [NT p_idlist'nt]%list
  | Nis'32 => [T DOT't; NT p_idlist'nt]%list
  | Nis'33 => [T ID't; T DOT't; NT p_idlist'nt]%list
  | Nis'34 => [T COLON't; T ID't; T DOT't; NT p_idlist'nt]%list
  | Nis'35 => [NT p_idlist'nt]%list
  | Nis'36 => [T COLON't; NT p_idlist'nt]%list
  | Nis'37 => [T COLON't; NT p_id'nt; NT p_FeatureCategory'nt; NT p_DirectionType'nt]%list
  | Nis'38 => []%list
  | Nis'39 => []%list
  | Nis'40 => []%list
  | Nis'41 => [NT p_idlist'nt]%list
  | Nis'42 => [T DOT't; NT p_idlist'nt]%list
  | Nis'43 => [NT p_ComponentCategory'nt]%list
  | Nis'44 => [NT p_ClassifierRef'nt; NT p_ComponentCategory'nt]%list
  | Nis'45 => [NT p_id'nt; NT p_ClassifierRef'nt; NT p_ComponentCategory'nt]%list
  | Nis'46 => [T COLON't; NT p_id'nt; NT p_ClassifierRef'nt; NT p_ComponentCategory'nt]%list
  | Nis'47 => [NT p_DeclarativeRef'nt; T COLON't; NT p_id'nt; NT p_ClassifierRef'nt; NT p_ComponentCategory'nt]%list
  | Nis'48 => [NT p_ImplRef'nt; T COLON't; NT p_id'nt; NT p_ComponentCategory'nt]%list
  end.
Extract Constant past_symb_of_non_init_state => "fun _ -> assert false".

Definition state_set_1 (s:state) : bool :=
  match s with
  | Init Init'0 | Ninit Nis'18 | Ninit Nis'22 => true
  | _ => false
  end.
Extract Inlined Constant state_set_1 => "assert false".

Definition state_set_2 (s:state) : bool :=
  match s with
  | Init Init'0 => true
  | _ => false
  end.
Extract Inlined Constant state_set_2 => "assert false".

Definition state_set_3 (s:state) : bool :=
  match s with
  | Ninit Nis'2 => true
  | _ => false
  end.
Extract Inlined Constant state_set_3 => "assert false".

Definition state_set_4 (s:state) : bool :=
  match s with
  | Ninit Nis'5 | Ninit Nis'27 | Ninit Nis'43 => true
  | _ => false
  end.
Extract Inlined Constant state_set_4 => "assert false".

Definition state_set_5 (s:state) : bool :=
  match s with
  | Ninit Nis'5 => true
  | _ => false
  end.
Extract Inlined Constant state_set_5 => "assert false".

Definition state_set_6 (s:state) : bool :=
  match s with
  | Ninit Nis'7 => true
  | _ => false
  end.
Extract Inlined Constant state_set_6 => "assert false".

Definition state_set_7 (s:state) : bool :=
  match s with
  | Ninit Nis'8 | Ninit Nis'29 | Ninit Nis'39 | Ninit Nis'45 => true
  | _ => false
  end.
Extract Inlined Constant state_set_7 => "assert false".

Definition state_set_8 (s:state) : bool :=
  match s with
  | Ninit Nis'9 | Ninit Nis'11 => true
  | _ => false
  end.
Extract Inlined Constant state_set_8 => "assert false".

Definition state_set_9 (s:state) : bool :=
  match s with
  | Ninit Nis'10 => true
  | _ => false
  end.
Extract Inlined Constant state_set_9 => "assert false".

Definition state_set_10 (s:state) : bool :=
  match s with
  | Ninit Nis'11 => true
  | _ => false
  end.
Extract Inlined Constant state_set_10 => "assert false".

Definition state_set_11 (s:state) : bool :=
  match s with
  | Ninit Nis'9 => true
  | _ => false
  end.
Extract Inlined Constant state_set_11 => "assert false".

Definition state_set_12 (s:state) : bool :=
  match s with
  | Ninit Nis'8 => true
  | _ => false
  end.
Extract Inlined Constant state_set_12 => "assert false".

Definition state_set_13 (s:state) : bool :=
  match s with
  | Ninit Nis'14 => true
  | _ => false
  end.
Extract Inlined Constant state_set_13 => "assert false".

Definition state_set_14 (s:state) : bool :=
  match s with
  | Ninit Nis'15 => true
  | _ => false
  end.
Extract Inlined Constant state_set_14 => "assert false".

Definition state_set_15 (s:state) : bool :=
  match s with
  | Ninit Nis'17 | Ninit Nis'46 => true
  | _ => false
  end.
Extract Inlined Constant state_set_15 => "assert false".

Definition state_set_16 (s:state) : bool :=
  match s with
  | Ninit Nis'18 | Ninit Nis'22 => true
  | _ => false
  end.
Extract Inlined Constant state_set_16 => "assert false".

Definition state_set_17 (s:state) : bool :=
  match s with
  | Ninit Nis'18 => true
  | _ => false
  end.
Extract Inlined Constant state_set_17 => "assert false".

Definition state_set_18 (s:state) : bool :=
  match s with
  | Ninit Nis'22 => true
  | _ => false
  end.
Extract Inlined Constant state_set_18 => "assert false".

Definition state_set_19 (s:state) : bool :=
  match s with
  | Ninit Nis'25 => true
  | _ => false
  end.
Extract Inlined Constant state_set_19 => "assert false".

Definition state_set_20 (s:state) : bool :=
  match s with
  | Ninit Nis'27 => true
  | _ => false
  end.
Extract Inlined Constant state_set_20 => "assert false".

Definition state_set_21 (s:state) : bool :=
  match s with
  | Ninit Nis'28 => true
  | _ => false
  end.
Extract Inlined Constant state_set_21 => "assert false".

Definition state_set_22 (s:state) : bool :=
  match s with
  | Ninit Nis'29 | Ninit Nis'45 => true
  | _ => false
  end.
Extract Inlined Constant state_set_22 => "assert false".

Definition state_set_23 (s:state) : bool :=
  match s with
  | Ninit Nis'30 => true
  | _ => false
  end.
Extract Inlined Constant state_set_23 => "assert false".

Definition state_set_24 (s:state) : bool :=
  match s with
  | Ninit Nis'31 => true
  | _ => false
  end.
Extract Inlined Constant state_set_24 => "assert false".

Definition state_set_25 (s:state) : bool :=
  match s with
  | Ninit Nis'32 => true
  | _ => false
  end.
Extract Inlined Constant state_set_25 => "assert false".

Definition state_set_26 (s:state) : bool :=
  match s with
  | Ninit Nis'33 => true
  | _ => false
  end.
Extract Inlined Constant state_set_26 => "assert false".

Definition state_set_27 (s:state) : bool :=
  match s with
  | Ninit Nis'35 => true
  | _ => false
  end.
Extract Inlined Constant state_set_27 => "assert false".

Definition state_set_28 (s:state) : bool :=
  match s with
  | Ninit Nis'29 => true
  | _ => false
  end.
Extract Inlined Constant state_set_28 => "assert false".

Definition state_set_29 (s:state) : bool :=
  match s with
  | Ninit Nis'39 => true
  | _ => false
  end.
Extract Inlined Constant state_set_29 => "assert false".

Definition state_set_30 (s:state) : bool :=
  match s with
  | Ninit Nis'40 => true
  | _ => false
  end.
Extract Inlined Constant state_set_30 => "assert false".

Definition state_set_31 (s:state) : bool :=
  match s with
  | Ninit Nis'41 => true
  | _ => false
  end.
Extract Inlined Constant state_set_31 => "assert false".

Definition state_set_32 (s:state) : bool :=
  match s with
  | Ninit Nis'43 => true
  | _ => false
  end.
Extract Inlined Constant state_set_32 => "assert false".

Definition state_set_33 (s:state) : bool :=
  match s with
  | Ninit Nis'44 => true
  | _ => false
  end.
Extract Inlined Constant state_set_33 => "assert false".

Definition state_set_34 (s:state) : bool :=
  match s with
  | Ninit Nis'45 => true
  | _ => false
  end.
Extract Inlined Constant state_set_34 => "assert false".

Definition state_set_35 (s:state) : bool :=
  match s with
  | Ninit Nis'46 => true
  | _ => false
  end.
Extract Inlined Constant state_set_35 => "assert false".

Definition state_set_36 (s:state) : bool :=
  match s with
  | Ninit Nis'17 => true
  | _ => false
  end.
Extract Inlined Constant state_set_36 => "assert false".

Definition past_state_of_non_init_state (s:noninitstate) : list (state -> bool) :=
  match s with
  | Nis'1 => [ state_set_1 ]%list
  | Nis'2 => [ state_set_2 ]%list
  | Nis'3 => [ state_set_3; state_set_2 ]%list
  | Nis'4 => [ state_set_2 ]%list
  | Nis'5 => [ state_set_2 ]%list
  | Nis'6 => [ state_set_4 ]%list
  | Nis'7 => [ state_set_5; state_set_2 ]%list
  | Nis'8 => [ state_set_6; state_set_5; state_set_2 ]%list
  | Nis'9 => [ state_set_7 ]%list
  | Nis'10 => [ state_set_8 ]%list
  | Nis'11 => [ state_set_9; state_set_8 ]%list
  | Nis'12 => [ state_set_10; state_set_9; state_set_8 ]%list
  | Nis'13 => [ state_set_11; state_set_7 ]%list
  | Nis'14 => [ state_set_12 ]%list
  | Nis'15 => [ state_set_13; state_set_12 ]%list
  | Nis'16 => [ state_set_14; state_set_13; state_set_12 ]%list
  | Nis'17 => [ state_set_12; state_set_6; state_set_5; state_set_2 ]%list
  | Nis'18 => [ state_set_15 ]%list
  | Nis'19 => [ state_set_16 ]%list
  | Nis'20 => [ state_set_16 ]%list
  | Nis'21 => [ state_set_17; state_set_15 ]%list
  | Nis'22 => [ state_set_16 ]%list
  | Nis'23 => [ state_set_18; state_set_16 ]%list
  | Nis'24 => [ state_set_16 ]%list
  | Nis'25 => [ state_set_16 ]%list
  | Nis'26 => [ state_set_19 ]%list
  | Nis'27 => [ state_set_19; state_set_16 ]%list
  | Nis'28 => [ state_set_20; state_set_19; state_set_16 ]%list
  | Nis'29 => [ state_set_21; state_set_20; state_set_19; state_set_16 ]%list
  | Nis'30 => [ state_set_22 ]%list
  | Nis'31 => [ state_set_23; state_set_22 ]%list
  | Nis'32 => [ state_set_24; state_set_23; state_set_22 ]%list
  | Nis'33 => [ state_set_25; state_set_24; state_set_23; state_set_22 ]%list
  | Nis'34 => [ state_set_26; state_set_25; state_set_24; state_set_23; state_set_22 ]%list
  | Nis'35 => [ state_set_23; state_set_22 ]%list
  | Nis'36 => [ state_set_27; state_set_23; state_set_22 ]%list
  | Nis'37 => [ state_set_28; state_set_21; state_set_20; state_set_19; state_set_16 ]%list
  | Nis'38 => [ state_set_16 ]%list
  | Nis'39 => [ state_set_16 ]%list
  | Nis'40 => [ state_set_29 ]%list
  | Nis'41 => [ state_set_30; state_set_29 ]%list
  | Nis'42 => [ state_set_31; state_set_30; state_set_29 ]%list
  | Nis'43 => [ state_set_29; state_set_16 ]%list
  | Nis'44 => [ state_set_32; state_set_29; state_set_16 ]%list
  | Nis'45 => [ state_set_33; state_set_32; state_set_29; state_set_16 ]%list
  | Nis'46 => [ state_set_34; state_set_33; state_set_32; state_set_29; state_set_16 ]%list
  | Nis'47 => [ state_set_35; state_set_34; state_set_33; state_set_32; state_set_29; state_set_16 ]%list
  | Nis'48 => [ state_set_36; state_set_12; state_set_6; state_set_5; state_set_2 ]%list
  end.
Extract Constant past_state_of_non_init_state => "fun _ -> assert false".

Definition items_of_state (s:state): list item := []%list.
Extract Constant items_of_state => "fun _ -> assert false".

Definition N_of_state (s:state) : N :=
  match s with
  | Init Init'0 => 0%N
  | Ninit Nis'1 => 1%N
  | Ninit Nis'2 => 2%N
  | Ninit Nis'3 => 3%N
  | Ninit Nis'4 => 4%N
  | Ninit Nis'5 => 5%N
  | Ninit Nis'6 => 6%N
  | Ninit Nis'7 => 7%N
  | Ninit Nis'8 => 8%N
  | Ninit Nis'9 => 9%N
  | Ninit Nis'10 => 10%N
  | Ninit Nis'11 => 11%N
  | Ninit Nis'12 => 12%N
  | Ninit Nis'13 => 13%N
  | Ninit Nis'14 => 14%N
  | Ninit Nis'15 => 15%N
  | Ninit Nis'16 => 16%N
  | Ninit Nis'17 => 17%N
  | Ninit Nis'18 => 18%N
  | Ninit Nis'19 => 19%N
  | Ninit Nis'20 => 20%N
  | Ninit Nis'21 => 21%N
  | Ninit Nis'22 => 22%N
  | Ninit Nis'23 => 23%N
  | Ninit Nis'24 => 24%N
  | Ninit Nis'25 => 25%N
  | Ninit Nis'26 => 26%N
  | Ninit Nis'27 => 27%N
  | Ninit Nis'28 => 28%N
  | Ninit Nis'29 => 29%N
  | Ninit Nis'30 => 30%N
  | Ninit Nis'31 => 31%N
  | Ninit Nis'32 => 32%N
  | Ninit Nis'33 => 33%N
  | Ninit Nis'34 => 34%N
  | Ninit Nis'35 => 35%N
  | Ninit Nis'36 => 36%N
  | Ninit Nis'37 => 37%N
  | Ninit Nis'38 => 38%N
  | Ninit Nis'39 => 39%N
  | Ninit Nis'40 => 40%N
  | Ninit Nis'41 => 41%N
  | Ninit Nis'42 => 42%N
  | Ninit Nis'43 => 43%N
  | Ninit Nis'44 => 44%N
  | Ninit Nis'45 => 45%N
  | Ninit Nis'46 => 46%N
  | Ninit Nis'47 => 47%N
  | Ninit Nis'48 => 48%N
  end.
End Aut.

Module MenhirLibParser := MenhirLib.Main.Make Aut.
Theorem safe:
  MenhirLibParser.safe_validator tt = true.
Proof eq_refl true<:MenhirLibParser.safe_validator tt = true.

Definition main : nat -> MenhirLibParser.Inter.buffer -> MenhirLibParser.Inter.parse_result       (AST.node) := MenhirLibParser.parse safe Aut.Init'0.

Theorem main_correct (log_fuel : nat) (buffer : MenhirLibParser.Inter.buffer):
  match main log_fuel buffer with
  | MenhirLibParser.Inter.Parsed_pr sem buffer_new =>
      exists word (tree : Gram.parse_tree (NT main'nt) word),
        buffer = MenhirLibParser.Inter.app_buf word buffer_new /\
        Gram.pt_sem tree = sem
  | _ => True
  end.
Proof. apply MenhirLibParser.parse_correct with (init:=Aut.Init'0). Qed.

