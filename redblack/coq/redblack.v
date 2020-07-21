From Coq Require Extraction.

Module Type SORTABLE.

    Parameter T: Type.

    Inductive Comparison: Type := LT | EQV | GT.

    Parameter compare: T -> T -> Comparison.

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

    Definition bind {A B: Type} (m: T A) (f: A -> T B): T B :=
        match m with
        | None =>
            None
        | Some a =>
            f a
        end.
End Option.




Inductive nat: Prop := O | S: nat -> nat.




Inductive ghost (A: Type): Prop :=
    makeGhost: A -> ghost A.

Definition
    useGhost {A: Type} {P: Prop} (g: ghost A) (f: A -> P): P
:=
    match g with
    | makeGhost _ a => f a
    end.





Module RedBlack (S: SORTABLE).

    (* Basic definitions. *)

    Inductive Color: Type := Red | Black.

    Inductive T0: Type :=
    | empty: T0
    | node: Color -> T0 -> S.T -> T0 -> T0.


    Inductive isValid: T0 -> Color -> nat -> Prop :=
    | validEmpty:
        isValid empty Black O

    | validRed:
        forall h t1 x t2,
            isValid t1 Black h
            -> isValid t2 Black h
            -> isValid (node Red t1 x t2) Red h

    | validBlack:
        forall h t1 c1 x t2 c2,
            isValid t1 c1 h
            -> isValid t2 c2 h
            -> isValid (node Black t1 x t2) Black (S h).


    Inductive RBT: Type :=
    | makeRBT:
        forall t c h, isValid t c h -> RBT.




    (* Insertion *)

    Definition trustMe {A: Type}: A.
    Admitted.

    Inductive Inserted: Type :=
        | insOk:
            forall t0 t1 h c,
                isValid t0 c h
                -> isValid t1 c h
                -> Inserted

        | insOkBlackRed:
            forall t0 t1 h,
                isValid t0 Black h
                -> isValid t1 Red h
                -> Inserted

        | insViolation:
            forall t0 h a (x: S.T) b (y: S.T) c,
                isValid t0 Red h
                -> isValid a Black h
                -> isValid b Black h
                -> isValid c Black h
                -> Inserted.


    Definition insertedToRBT (ins: Inserted): RBT :=
        match ins with
        | insOk _ _ _ _ _ valid =>
            makeRBT _ _ _ valid

        | insOkBlackRed _ _ _ _ valid =>
            makeRBT _ _ _ valid

        | insViolation _ _ _ x _ y _ _ va vb vc =>
            makeRBT _ _ _
                (
                    validBlack _ _ _ x _ _
                        va
                        (validRed _ _ y _ vb vc)
                )
        end.


    Fixpoint
        insert_aux (e: S.T) (tree: T0)
        : forall c h,
            isValid tree c h
            -> option Inserted
    :=
        match tree with
        | empty =>
            fun _ _ _ =>
            Some (
                insOkBlackRed _ _ _
                    validEmpty
                    (validRed _ _ e _ validEmpty validEmpty)
            )
        | node _ a x _ =>
            match S.compare e x with
            | S.LT =>
                fun c h valid =>
                Option.bind
                    (insert_aux e a trustMe trustMe trustMe)
                    (fun anew => trustMe)
            | S.EQV =>
                fun _ _ _ => None
            | S.GT =>
                trustMe
            end
        end.



    Definition insert (e: S.T) (tree: RBT): option RBT :=
        match tree with
        | makeRBT t _ _ valid =>
            Option.map
                insertedToRBT
                (insert_aux e _ _ _ valid)
        end.
End RedBlack.
