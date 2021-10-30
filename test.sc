import io.shiftleft.codepropertygraph.generated.nodes.{Call, Method}
import io.shiftleft.semanticcpg.language._
import overflowdb.traversal.Traversal

def x = cpg.call.groupBy(arg =>
  arg.argument.argumentIndex(1).astParent.isCall.callee.caller.code.l
).map { case (key, args) =>

  (key, args.code.l)
}

println(x)