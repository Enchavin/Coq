(*定义类型 day*)
Inductive day : Type :=
    |monday
    |tuesday
    |thursday
    |wednesday
    |friday
    |saturday
    |sunday.

Definition next_weekday (d:day) : day :=
    match d with
    |monday => tuesday
    |tuesday => wednesday
    |wednesday => thursday
    |thursday => friday
    |friday => monday
    |saturday => monday
    |sunday => monday
    end.

(*通过Compute命令计算next_weekday表达式的值*)
Compute (next_weekday friday).
Compute (next_weekday (next_weekday saturday)).

(*期望的结果*)
(*先定义一个断言assertion，名字叫做test_next_weekday，方便以后引用*)
Example test_next_weekday:
    (next_weekday (next_weekday saturday)) = tuesday.
(*通过Proof来证明断言的正确性*)
Proof. simpl. reflexivity. Qed.

(*定义布尔类型*)
Inductive bool : Type :=
    |true
    |false.

Definition  negb (b:bool) : bool :=
    match b with
    |true => false
    |fasle => true
    end.

Definition andb (b1:bool)(b2:bool) : bool :=
    match b1 with
    |true => b2
    |false => false
    end.

Definition orb (b1:bool)(b2:bool) : bool :=
    match b1 with
    |true => true
    |false => b2
    end.



