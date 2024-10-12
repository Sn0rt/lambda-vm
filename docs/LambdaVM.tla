---- MODULE LambdaVM ----
EXTENDS Naturals, Sequences, TLC

CONSTANT VMMaxDepth, MaxExprDepth, Variables, MaxSubstituteDepth
VARIABLE expr, vmDepth, vmEvalStack, callStack
ASSUME Variables \subseteq STRING

(* Lambda expressions *)
RECURSIVE Expr(_)
Expr(depth) ==
    IF depth = 0 THEN
        [type: {"Variable", "Empty"}, name: Variables]
    ELSE
        LET SubExpr == Expr(depth - 1) IN
        [type: {"Variable", "Empty"}, name: Variables] \union
        [type: {"Abstraction"}, param: Variables, body: SubExpr] \union
        [type: {"Application"}, func: SubExpr, arg: SubExpr]

LambdaExpr == Expr(MaxExprDepth)

(* Recursive Substitute function with depth limit *)
RECURSIVE SubstituteRec(_, _, _, _)
SubstituteRec(e, x, v, depth) ==
    IF depth = 0 THEN e
    ELSE CASE e.type = "Variable" ->
            IF e.name = x THEN v ELSE e
         [] e.type = "Abstraction" ->
            IF e.param = x THEN e
            ELSE [type |-> "Abstraction",
                  param |-> e.param,
                  body |-> SubstituteRec(e.body, x, v, depth - 1)]
         [] e.type = "Application" ->
            [type |-> "Application",
             func |-> SubstituteRec(e.func, x, v, depth - 1),
             arg |-> SubstituteRec(e.arg, x, v, depth - 1)]

Substitute(e, x, v) == SubstituteRec(e, x, v, MaxSubstituteDepth)

VMTypeOK ==
    /\ expr \in LambdaExpr
    /\ vmDepth \in 0..VMMaxDepth
    /\ vmEvalStack \in Seq(LambdaExpr)
    /\ callStack \in Seq([expr: LambdaExpr, context: [param: STRING, arg: LambdaExpr \union [type: {"Empty"}]]])

VMInit ==
    /\ expr = [type |-> "Application",
               func |-> [type |-> "Abstraction",
                         param |-> "x",
                         body |-> [type |-> "Variable", name |-> "x"]],
               arg |-> [type |-> "Variable", name |-> "y"]]
    /\ vmDepth = 0
    /\ vmEvalStack = <<expr>>
    /\ callStack = <<>>

RECURSIVE FreeVariables(_)
FreeVariables(e) ==
    CASE e.type = "Variable" -> {e.name}
      [] e.type = "Abstraction" -> FreeVariables(e.body) \ {e.param}
      [] e.type = "Application" -> FreeVariables(e.func) \union FreeVariables(e.arg)

VMEvalStep ==
    /\ vmDepth < VMMaxDepth
    /\ \/ /\ Len(vmEvalStack) > 0
          /\ LET top == Head(vmEvalStack)
             IN CASE top.type = "Application" ->
                    /\ vmEvalStack' = <<top.func>> \o vmEvalStack
                    /\ callStack' = <<[expr |-> top.arg, context |-> [param |-> "", arg |-> top.arg]]>> \o callStack
                    /\ vmDepth' = vmDepth + 1
                [] top.type = "Abstraction" ->
                    IF Len(callStack) > 0 /\ Head(callStack).context.param = "" THEN
                        LET context == Head(callStack).context
                            newExpr == Substitute(top.body, top.param, context.arg)
                        IN /\ vmEvalStack' = <<newExpr>> \o Tail(vmEvalStack)
                           /\ callStack' = Tail(callStack)
                           /\ vmDepth' = vmDepth + 1
                    ELSE
                        UNCHANGED <<vmEvalStack, callStack, vmDepth>>
                [] top.type = "Variable" ->
                    UNCHANGED <<vmEvalStack, callStack, vmDepth>>
       \/ /\ Len(vmEvalStack) = 0
          /\ UNCHANGED <<vmEvalStack, callStack, vmDepth>>
    /\ UNCHANGED <<expr>>

VMNext ==
    \/ VMEvalStep
    \/ /\ vmDepth >= VMMaxDepth
       /\ UNCHANGED <<expr, vmDepth, vmEvalStack, callStack>>

VMSpec == VMInit /\ [][VMNext]_<<expr, vmDepth, vmEvalStack, callStack>>

THEOREM VMSpec => []VMTypeOK

====
