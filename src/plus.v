(* Plus relation for words in Lambek calculus *)

Inductive Plus : Word -> Prop := 
  | slash : forall A B, (Plus A) -> (Minus B) -> (Plus (A++B))
  | backslash : forall A B, (Plus A) -> (Minus B) -> (Plus (B++[BL 0 1]++A))
  | pvi : forall v ne, (Nat.Even ne) -> Plus ([BL v ne])
  | pmp : forall A B, (Plus A) -> (Minus B) -> (Plus (A++(dneg B))).
