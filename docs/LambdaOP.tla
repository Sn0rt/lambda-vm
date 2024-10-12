---- MODULE LambdaOP ----
EXTENDS Naturals, Sequences, TLC

CONSTANT MaxDepth

VARIABLE evalStack, depth, currentOp

ToNumber(churchNumeral) ==
    CASE churchNumeral.type = "ChurchNumeral" -> churchNumeral.value
      [] OTHER -> 0

Max(a, b) == IF a > b THEN a ELSE b

(* Basic Lambda Calculus *)
Variable(name) == [type |-> "Variable", value |-> name, left |-> [type |-> "", value |-> ""], right |-> [type |-> "", value |-> ""]]

Abstraction(param, body) == [type |-> "Abstraction", value |-> "lambda", left |-> Variable(param), right |-> body]

Application(func, arg) == [type |-> "Application", value |-> "apply", left |-> func, right |-> arg]

(* Church Numerals *)
ChurchNumeral(n) ==
    [type |-> "ChurchNumeral",
     value |-> n,
     left |-> [type |-> "", value |-> ""],
     right |-> [type |-> "", value |-> ""]]

Succ ==
    [type |-> "Builtin", value |-> "succ",
     left |-> [type |-> "", value |-> ""],
     right |-> [type |-> "", value |-> ""]]

Pred ==
    [type |-> "Builtin", value |-> "pred",
     left |-> [type |-> "", value |-> ""],
     right |-> [type |-> "", value |-> ""]]

IsZero ==
    [type |-> "Builtin", value |-> "is_zero",
     left |-> [type |-> "", value |-> ""],
     right |-> [type |-> "", value |-> ""]]

Multiply ==
    [type |-> "Builtin", value |-> "multiply",
     left |-> [type |-> "", value |-> ""],
     right |-> [type |-> "", value |-> ""]]

(* Church Booleans *)
ChurchTrue ==
    Abstraction("x", Abstraction("y", Variable("x")))

ChurchFalse ==
    Abstraction("x", Abstraction("y", Variable("y")))

And ==
    [type |-> "Builtin", value |-> "and",
     left |-> [type |-> "", value |-> ""],
     right |-> [type |-> "", value |-> ""]]

Or ==
    [type |-> "Builtin", value |-> "or",
     left |-> [type |-> "", value |-> ""],
     right |-> [type |-> "", value |-> ""]]

Not ==
    [type |-> "Builtin", value |-> "not",
     left |-> [type |-> "", value |-> ""],
     right |-> [type |-> "", value |-> ""]]

(* Control Flow *)
IfThenElse ==
    [type |-> "Builtin", value |-> "ifthenelse",
     left |-> [type |-> "", value |-> ""],
     right |-> [type |-> "", value |-> ""]]

(* Pairs *)
Pair ==
    [type |-> "Builtin", value |-> "pair",
     left |-> [type |-> "", value |-> ""],
     right |-> [type |-> "", value |-> ""]]

First ==
    [type |-> "Builtin", value |-> "first",
     left |-> [type |-> "", value |-> ""],
     right |-> [type |-> "", value |-> ""]]

Second ==
    [type |-> "Builtin", value |-> "second",
     left |-> [type |-> "", value |-> ""],
     right |-> [type |-> "", value |-> ""]]

(* Recursion *)
YCombinator ==
    [type |-> "Builtin", value |-> "Y",
     left |-> [type |-> "", value |-> ""],
     right |-> [type |-> "", value |-> ""]]

EvalSucc ==
    /\ Len(evalStack) > 0
    /\ depth < MaxDepth
    /\ LET n == Head(evalStack)
       IN /\ evalStack' = Tail(evalStack) \o <<ChurchNumeral(ToNumber(n) + 1)>>
          /\ depth' = depth + 1

EvalPred ==
    /\ Len(evalStack) > 0
    /\ depth < MaxDepth
    /\ LET n == Head(evalStack)
       IN /\ evalStack' = Tail(evalStack) \o <<ChurchNumeral(Max(0, ToNumber(n) - 1))>>
          /\ depth' = depth + 1

EvalIsZero ==
    /\ Len(evalStack) > 0
    /\ LET n == Head(evalStack)
       IN /\ evalStack' = Tail(evalStack) \o <<IF ToNumber(n) = 0 THEN ChurchTrue ELSE ChurchFalse>>
          /\ depth' = depth + 1

EvalMultiply ==
    /\ Len(evalStack) > 1
    /\ depth < MaxDepth
    /\ LET n == Head(evalStack)
           m == Head(Tail(evalStack))
       IN /\ evalStack' = Tail(Tail(evalStack)) \o <<ChurchNumeral(ToNumber(n) * ToNumber(m))>>
          /\ depth' = depth + 1

EvalAnd ==
    /\ Len(evalStack) > 1
    /\ LET b1 == Head(evalStack)
           b2 == Head(Tail(evalStack))
       IN /\ evalStack' = Tail(Tail(evalStack)) \o <<IF b1 = ChurchTrue /\ b2 = ChurchTrue THEN ChurchTrue ELSE ChurchFalse>>
          /\ depth' = depth + 1

EvalOr ==
    /\ Len(evalStack) > 1
    /\ LET b1 == Head(evalStack)
           b2 == Head(Tail(evalStack))
       IN /\ evalStack' = Tail(Tail(evalStack)) \o <<IF b1 = ChurchTrue \/ b2 = ChurchTrue THEN ChurchTrue ELSE ChurchFalse>>
          /\ depth' = depth + 1

EvalNot ==
    /\ Len(evalStack) > 0
    /\ LET b == Head(evalStack)
       IN /\ evalStack' = Tail(evalStack) \o <<IF b = ChurchTrue THEN ChurchFalse ELSE ChurchTrue>>
          /\ depth' = depth + 1

EvalIfThenElse ==
    /\ Len(evalStack) > 2
    /\ LET condition == Head(evalStack)
           thenBranch == Head(Tail(evalStack))
           elseBranch == Head(Tail(Tail(evalStack)))
       IN /\ evalStack' = Tail(Tail(Tail(evalStack))) \o <<IF condition = ChurchTrue THEN thenBranch ELSE elseBranch>>
          /\ depth' = depth + 1

EvalPair ==
    /\ Len(evalStack) > 1
    /\ LET first == Head(evalStack)
           second == Head(Tail(evalStack))
       IN /\ evalStack' = Tail(Tail(evalStack)) \o <<[type |-> "Pair", left |-> first, right |-> second]>>
          /\ depth' = depth + 1

EvalFirst ==
    /\ Len(evalStack) > 0
    /\ LET pair == Head(evalStack)
       IN /\ evalStack' = Tail(evalStack) \o <<pair.left>>
          /\ depth' = depth + 1

EvalSecond ==
    /\ Len(evalStack) > 0
    /\ LET pair == Head(evalStack)
       IN /\ evalStack' = Tail(evalStack) \o <<pair.right>>
          /\ depth' = depth + 1

EvalYCombinator ==
    (* Y combinator implementation *)
    UNCHANGED <<evalStack, depth>>

Init ==
    /\ evalStack = <<ChurchNumeral(3), ChurchNumeral(2)>>
    /\ depth = 0
    /\ currentOp = "none"

Next ==
    /\ depth < MaxDepth
    /\ \/ /\ currentOp = "none"
          /\ \/ /\ currentOp' = "succ"
                /\ UNCHANGED <<evalStack, depth>>
             \/ /\ currentOp' = "pred"
                /\ UNCHANGED <<evalStack, depth>>
             \/ /\ currentOp' = "multiply"
                /\ UNCHANGED <<evalStack, depth>>
             \/ /\ UNCHANGED <<currentOp, evalStack, depth>>
       \/ /\ currentOp = "succ"
          /\ EvalSucc
          /\ currentOp' = "none"
       \/ /\ currentOp = "pred"
          /\ EvalPred
          /\ currentOp' = "none"
       \/ /\ currentOp = "multiply"
          /\ EvalMultiply
          /\ currentOp' = "none"
    \/ /\ depth >= MaxDepth
       /\ UNCHANGED <<evalStack, depth, currentOp>>

Termination == depth >= MaxDepth

Spec == Init /\ [][Next]_<<evalStack, depth, currentOp>> /\ WF_<<evalStack, depth, currentOp>>(Next) /\ SF_<<evalStack, depth, currentOp>>(Termination)

TypeOK ==
    /\ evalStack \in Seq([type: {"ChurchNumeral"},
                          value: Nat,
                          left: [type: STRING, value: STRING],
                          right: [type: STRING, value: STRING]])
    /\ depth \in 0..MaxDepth
    /\ currentOp \in {"none", "succ", "pred", "multiply"}

DepthInvariant == depth <= MaxDepth

THEOREM Spec => [](TypeOK /\ DepthInvariant)

====
