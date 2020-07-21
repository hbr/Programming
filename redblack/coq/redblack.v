Module Type SORTABLE.

    Parameter T: Type.

    Inductive Comparison: Type := LT | EQV | GT.

    Parameter compare: T -> Comparison.

End SORTABLE.


Module Option.
    Definition T (A: Type): Type := option A.

    Definition map {A B: Type} (f: A -> B) (o: T A): T B :=
        match o with
        | None =>
            None
        | Some v =>
            Some (f v)
        end.
End Option.

Module RedBlack (S: SORTABLE).


    (* Basic definitions. *)

    Inductive Color: Type := Red | Black.

    Definition increase (c: Color) (h: nat): nat :=
        match c with
        | Red =>
            h
        | Black =>
            S h
        end.

    Module Tree.
        Inductive T: Type :=
        | empty: T
        | node: Color -> T -> S.T -> T -> T.

        Fixpoint blackHeight (tree: T): nat :=
            match tree with
            | empty =>
                O
            | node color t1 _ _ =>
                increase color (blackHeight t1)
            end.

        Definition color (tree: T): Color :=
            match tree with
            | empty =>
                Black
            | node c _ _ _ =>
                c
            end.

        Definition isRed (tree: T): Prop :=
            color tree = Red.

        Definition isBlack (tree: T): Prop :=
            color tree = Black.

        Definition sameHeight (t1 t2: T): Prop :=
            blackHeight t1 = blackHeight t2.

        Definition sameColor (t1 t2: T): Prop :=
            color t1 = color t2.
    End Tree.


    Inductive isValid: Tree.T -> Color -> nat -> Prop :=
    | validEmpty:
        isValid Tree.empty Black O

    | validRed:
        forall h t1 x t2,
            isValid t1 Black h
            -> isValid t2 Black h
            -> isValid (Tree.node Red t1 x t2) Red h

    | validBlack:
        forall h t1 c1 x t2 c2,
            isValid t1 c1 h
            -> isValid t2 c2 h
            -> isValid (Tree.node Black t1 x t2) Black (S h).


    Definition isValid0 (tree: Tree.T): Prop :=
        isValid tree (Tree.color tree) (Tree.blackHeight tree).


    Theorem validToValid0:
        forall t h c, isValid t c h -> isValid0 t.
    Admitted.


    Inductive RBT: Type :=
    | makeRBT:
        forall tree, isValid0 tree -> RBT.


    Definition validToRBT t h c (valid: isValid t c h): RBT :=
        makeRBT _ (validToValid0 _ _ _ valid).






    (* Insertion *)

    Definition trustMe {A: Type}: A.
    Admitted.

    Inductive Inserted: Tree.T -> Type :=
        | insOk:
            forall t0 t1,
                let h := Tree.blackHeight t0 in
                let c := Tree.color t0 in
                isValid t0 c h
                -> isValid t1 c h
                -> Inserted t0

        | insOkBlackRed:
            forall t0 t1,
                let h := Tree.blackHeight t0 in
                isValid t0 Black h
                -> isValid t1 Red h
                -> Inserted t0

        | insViolation:
            forall t0 a (x: S.T) b (y: S.T) c,
                let h := Tree.blackHeight t0 in
                isValid t0 Red h
                -> isValid a Black h
                -> isValid b Black h
                -> isValid c Black h
                -> Inserted t0.


    Definition insertedToRBT tree (ins: Inserted tree): RBT :=
        match ins with
        | insOk _ _ _ valid =>
            validToRBT _ _ _ valid

        | insOkBlackRed _ _ _ _ valid =>
            validToRBT _ _ _ valid

        | insViolation _ _ x _ y _ _ va vb vc =>
            validToRBT _ _ _
                (
                    validBlack _ _ _ x _ _
                        va
                        (validRed _ _ y _ vb vc)
                )
        end.


    Definition
        insert_aux (e: S.T) (tree: Tree.T)
        : isValid0 tree -> option (Inserted tree) :=
            trustMe.


    Definition
        insert_aux2 (e: S.T) (tree: Tree.T)
        : forall h c,
            isValid tree c h
            -> option (Inserted tree)
        :=
            trustMe.



    Definition insert (e: S.T) (tree: RBT): option RBT :=
        match tree with
        | makeRBT t valid =>
            Option.map
                (insertedToRBT t)
                (insert_aux e t valid)
        end.
End RedBlack.
