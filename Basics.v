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
Proof. 
    simpl.
    reflexivity. 
Qed.

(*定义布尔类型*)
Inductive bool : Type :=
    |true
    |false.

Definition negb (b:bool) : bool :=
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

(*对上述布尔函数进行测试*)
Example test_orb1: 
    (orb true false) = true.
Proof.
    simpl.
    reflexivity.
Qed.
Example test_orb2:
    (orb false false) = false.
Proof.
    simpl.
    reflexivity.
Qed.
Example test_orb3:
    (orb false true) = true.
Proof.
    simpl.
    reflexivity.
Qed.

Example test_orb4:
    (orb true true) = true.
Proof.
    simpl.
    reflexivity.
Qed.

(*使用Notation简化Definition*)
Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).

Example test_orb5:
    false || false || true = true.
Proof.
    simpl.
    reflexivity.
Qed.

(*条件表达式*)
Definition negb' (b:bool) : bool:=
    if b
        then false
    else 
        true.

Definition andb' (b1:bool)(b2:bool) : bool:=
    if b1
        then b2
    else
        false.

Definition orb' (b1:bool)(b2:bool) : bool:=
    if b1
        then true
    else
        b2.

(*练习1，nandb*)
Definition nandb (b1:bool)(b2:bool) : bool:=
    match b1 with
    |true => negb b2
    |false => true
    end.
Example test_nandb1: 
    (nandb true false) = true.
Proof.
    simpl.
    reflexivity.
Qed.
Example test_nandb2: 
    (nandb false false) = true.
Proof.
    simpl.
    reflexivity.
Qed.
Example test_nandb3: 
    (nandb false true) = true.
Proof.
    simpl.
    reflexivity.
Qed.
Example test_nandb4: 
    (nandb true true) = false.
Proof.
    simpl.
    reflexivity.
Qed.

(*练习2，andb3*)
Definition andb3 (b1:bool)(b2:bool)(b3:bool) : bool :=
    match b1 with
    |true => andb b2 b3
    |false => false
    end.
Example test_andb31: 
    (andb3 true true true) = true.
Proof.
    simpl.
    reflexivity.
Qed.
Example test_andb32: 
    (andb3 false true true) = false.
Proof.
    simpl.
    reflexivity.
Qed.
Example test_andb33: 
    (andb3 true false true) = false.
Proof.
    simpl.
    reflexivity.
Qed.
Example test_andb34: 
    (andb3 true true false) = false.
Proof.
    simpl.
    reflexivity.
Qed.

(*类型Type，包括表达式和函数*)
Check true.
Check true : bool.
Check (negb true) : bool.
Check negb : bool -> bool.

(*由旧类型构造新类型，类似于复合定义*)
Inductive rgb : Type :=
    |red
    |green
    |blue.

Inductive color : Type :=
    |black
    |white
    |primary (p:rgb).

Definition monochrome (c:color) : bool :=
    match c with
    |black => true
    |white => true
    |primary p => false
    end.

Definition isred (c:color) : bool :=
    match c with
    |black => false
    |white => false
    |primary red => true
    |primary _ => false
    end.

(*模块Modules*)
Module Playground.
    Definition b : rgb := blue.        
End Playground.

Definition b : bool := true.
Check b : bool.

(*元组Tuples*)
Module TuplePlayground.
Inductive bit : Type :=
    |B0
    |B1.

Inductive nybble : Type :=
    |bits (b0 b1 b2 b3 : bit).

Check (bits B1 B0 B1 B0) : nybble.

Definition all_zero (nb : nybble) : bool :=
    match nb with
    |(bits B0 B0 B0 B0) => true
    |(bits _ _ _ _) => false
    end.

Compute (all_zero (bits B1 B0 B1 B0)).
Compute (all_zero (bits B0 B0 B0 B0)).
End TuplePlayground.

(*自然数Numbers*)
Module NatPlayground.
Inductive nat : Type :=
    |O
    |S (n : nat).

Inductive nat' : Type :=
    |stop
    |tick (foo : nat').

Check tick stop.
