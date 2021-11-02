import io.shiftleft.codepropertygraph.Cpg
import io.shiftleft.codepropertygraph.generated.nodes.Call
import io.shiftleft.semanticcpg.language._
import overflowdb.traversal.Traversal
import scalax.collection.Graph
import scalax.collection.GraphPredef.EdgeAssoc
import scalax.collection.edge.Implicits.any2XEdgeAssoc
import scalax.collection.edge.LDiEdge
import scalax.collection.io.dot._
import java.io.PrintWriter
import scala.collection.mutable.ListBuffer

import $ivy.`org.scala-graph:graph-core_2.13:1.13.3`
import $ivy.`org.scala-graph:graph-dot_2.13:1.13.0`

def cpg_typed: Cpg = cpg

def escape(raw: String): String = {
  import org.apache.commons.lang.StringEscapeUtils.escapeJava
  escapeJava(raw)
}

object EdgeType extends Enumeration {
  type EdgeType = Value
  val IndirectSource, IndirectSourceCall, Call, Parameter, Return, Sink = Value
}

import EdgeType._

object TaintNodeType extends Enumeration {
  type TaintNodeType = Value
  val Argument, Parameter, Return, Call, Sink = Value
}
import TaintNodeType._

case class TaintNode(id: Long, nodeType: TaintNodeType, isSource: Boolean)

var taintGraph: Graph[TaintNode, LDiEdge] = Graph()

def getArgumentFromId(id: Long) = cpg_typed.argument.id(id)
def getArgumentMethod(id: Long) = getArgumentFromId(id).call.inAst.isMethod

def getParameterFromId(id: Long) = cpg_typed.parameter.id(id)
def getParameterMethod(id: Long) = getParameterFromId(id).method

def getReturnFromId(id: Long) = cpg_typed.ret.id(id)
def getReturnMethod(id: Long) = getReturnFromId(id).method

def getCallFromId(id: Long) = cpg_typed.call.id(id)
def getCallMethod(id: Long) = getCallFromId(id).method

def getMethod(node: TaintNode) =
  node.nodeType match {
    case TaintNodeType.Argument => getArgumentMethod(node.id)
    case TaintNodeType.Parameter => getParameterMethod(node.id)
    case TaintNodeType.Return => getReturnMethod(node.id)
    case TaintNodeType.Call => getCallMethod(node.id)
  }

def getCode(node: TaintNode) =
  node.nodeType match {
    case TaintNodeType.Argument => getArgumentFromId(node.id).code.head
    case TaintNodeType.Parameter => getParameterFromId(node.id).name.head
    case TaintNodeType.Return => getReturnFromId(node.id).astChildren.code.head
    case TaintNodeType.Call => getCallFromId(node.id).code.head
  }

def renderNode(node: TaintNode) =
  node.nodeType match {
    case TaintNodeType.Argument =>
      def arg = getArgumentFromId(node.id)

      s"""${arg.call.inAst.isMethod.filename.head}#${arg.call.lineNumber.head} \n\\"${escape(arg.call.code.head)}\\" ${escape(arg.code.head)}"""
    case TaintNodeType.Parameter =>
      def param = getParameterFromId(node.id)

      s"""${param.method.filename.head}#${param.lineNumber.head} \n\\"${escape(param.method.code.head)}\\" ${escape(param.name.head)}"""
    case TaintNodeType.Return =>
      def ret = getReturnFromId(node.id)

      s"""${ret.method.filename.head}#${ret.lineNumber.head} \n\\"${escape(ret.code.head)}\\" ${escape(ret.astChildren.code.head)}"""
    case TaintNodeType.Call =>
      def call = getCallFromId(node.id)

      s"""${call.method.filename.head}#${call.lineNumber.head} \n\\"${escape(call.code.head)}\\""""
    case TaintNodeType.Sink =>
      def call = getCallFromId(node.id)

      s"""${call.method.filename.head}#${call.lineNumber.head} \n\\"${escape(call.code.head)}\\""""
  }

def getNodeAttrList(node: TaintNode) = {
  var attrList: ListBuffer[DotAttr] = ListBuffer()

  if (!node.isSource && node.nodeType != TaintNodeType.Sink) {
    attrList += DotAttr(Id("shape"), Id("plain"))
  } else {
    node.nodeType match {
      case TaintNodeType.Argument =>

      case TaintNodeType.Parameter =>

      case TaintNodeType.Return =>

      case TaintNodeType.Call =>

      case TaintNodeType.Sink =>
        attrList += DotAttr(Id("shape"), Id("diamond"))
    }
  }

  attrList.toSeq
}

def getEdgeAttrList(edge: LDiEdge[Graph[TaintNode, LDiEdge]#NodeT]) = {
  var attrList: ListBuffer[DotAttr] = ListBuffer()
  attrList += DotAttr(Id("label"), Id(edge.label.toString))

  attrList.toSeq
}

def exportPrettyTaintGraph(taintGraph: Graph[TaintNode, LDiEdge]) = {
  val dotRoot = DotRootGraph(
    directed = true,
    id = Some(Id("TaintDot")),
    attrList = Seq(
      DotAttr(Id("nodesep"), Id("1.5")),
      DotAttr(Id("ranksep"), Id("1.5")),
    )
  )

  def edgeTransformer(innerEdge: Graph[TaintNode, LDiEdge]#EdgeT): Option[(DotGraph, DotEdgeStmt)] = {
    val edge = innerEdge.edge
    Some(
      dotRoot,
      DotEdgeStmt(
        NodeId(renderNode(edge.from.value)),
        NodeId(renderNode(edge.to.value)),
        getEdgeAttrList(edge)
      )
    )
  }

  def nodeTransformer(innerNode: Graph[TaintNode, LDiEdge]#NodeT): Option[(DotGraph, DotNodeStmt)] =
    Some(dotRoot, DotNodeStmt(NodeId(renderNode(innerNode.value)), getNodeAttrList(innerNode.value)))

  taintGraph.toDot(
    dotRoot,
    edgeTransformer,
    iNodeTransformer = Some(nodeTransformer),
    cNodeTransformer = Some(nodeTransformer),
  )
}

def exportTaintGraph(taintGraph: Graph[TaintNode, LDiEdge]) = {
  val dotRoot = DotRootGraph(
    directed = true,
    id = Some(Id("TaintDot")),
  )

  def edgeTransformer(innerEdge: Graph[TaintNode, LDiEdge]#EdgeT): Option[(DotGraph, DotEdgeStmt)] = {
    val edge = innerEdge.edge
    Some(
      dotRoot,
      DotEdgeStmt(
        NodeId(edge.from.toString),
        NodeId(edge.to.toString),
        getEdgeAttrList(edge)
      )
    )
  }

  def nodeTransformer(innerNode: Graph[TaintNode, LDiEdge]#NodeT): Option[(DotGraph, DotNodeStmt)] =
    Some(dotRoot, DotNodeStmt(NodeId(innerNode.toString)))

  taintGraph.toDot(
    dotRoot,
    edgeTransformer,
    iNodeTransformer = Some(nodeTransformer)
  )
}

// Map[Function name, Buf Index]
var sourceOperations: Map[String, Int] = Map(
  "recv" -> 2,
  "recvfrom" -> 2,
  "WSARecvEx" -> 2,
  "HttpQueryInfo" -> 3,
  "HttpQueryInfoA" -> 3,
  "HttpQueryInfoW" -> 3,
  "InternetReadFile" -> 2,
  "InternetReadFileExA" -> 2,
  "InternetReadFileExW" -> 2,
)

// Map[Function name, Buf Index]
val sinkOperations: Map[String, Int] = Map(
  "atoi" -> 1,
  "_wtoi" -> 1,
  "atoi_l" -> 1,
  "_wtoi_l" -> 1,
  "strlen" -> 1,
  "strcpy" -> 1,
  "wcscpy" -> 1,
  "_mbscpy" -> 1,
  "lstrcat" -> 1,
  "lstrcatA" -> 1,
  "lstrcatW" -> 1,
  "lstrcpy" -> 1,
  "lstrcpyA" -> 1,
  "lstrcpyW" -> 1,
  "lstrcpyn" -> 1,
  "lstrcpynA" -> 1,
  "lstrcpynW" -> 1,
  "lstrlen" -> 1,
  "lstrlenA" -> 1,
  "lstrlenW" -> 1,
  "_atodbl" -> 2,
  "_atodbl_l" -> 2,
  "_atoldbl" -> 2,
  "_atoldbl_l" -> 2,
  "_atoflt" -> 2,
  "_atoflt_l" -> 2,
  "atof" -> 1,
  "_atof_l" -> 1,
  "_wtof" -> 1,
  "_wtof_l" -> 1,
  "_atoi64" -> 1,
  "_wtoi64" -> 1,
  "_atoi64_l" -> 1,
  "_wtoi64_l" -> 1,
  "atol" -> 1,
  "_atol_l" -> 1,
  "_wtol" -> 1,
  "_wtol_l" -> 1,
  "atoll" -> 1,
  "_wtoll" -> 1,
  "_atoll_l" -> 1,
  "_wtoll_l" -> 1,
)

// Map[Function name, Src Index, Dst Index]
val indirectSourceOperations: Map[(String, Int), Int] = Map(
  ("memcpy", 2) -> 1,
  ("<operator>.assignment", 2) -> 1,
  ("strcpy", 2) -> 1,
  ("wcscpy", 2) -> 1,
  ("_mbscpy", 2) -> 1,
  ("lstrcat", 2) -> 1,
  ("lstrcatA", 2) -> 1,
  ("lstrcatW", 2) -> 1,
  ("lstrcpy", 2) -> 1,
  ("lstrcpyA", 2) -> 1,
  ("lstrcpyW", 2) -> 1,
  ("lstrcpyn", 2) -> 1,
  ("lstrcpynA", 2) -> 1,
  ("lstrcpynW", 2) -> 1,
)

// Map[Function name, Src Index]
val indirectSourceOperationsCall: Map[String, Int] = Map(
  "<operator>.indirectIndexAccess" -> 1,
  "<operator>.cast" -> 2,
  "<operator>.addition" -> 1,
  "<operator>.addressOf" -> 1,
  "<operator>.indirection" -> 1,
)

// Map[Function name, source name Index]
val sourceCreator: Map[String, Int] = Map(
  "GetProcAddress" -> 2
)

def filterCalls(calls: Traversal[Call], operations: Map[String, Int]) =
  calls.nameExact(operations.keys.toSeq: _*)

def getArgs(c: Call, operations: Map[String, Int]) =
  c.argument.argumentIndex(operations(c.name))

def getSource(calls: Traversal[Call], operations: Map[String, Int]): List[TaintNode] =
  filterCalls(calls, operations)
    .map(node => TaintNode(getArgs(node, operations).id.head, TaintNodeType.Argument, isSource = true)).l


def getIndirectSource(nodes: Graph[TaintNode, LDiEdge]#NodeSetT, operations: Map[(String, Int), Int]): List[LDiEdge[TaintNode]] =
  nodes.flatMap((taintNode: Graph[TaintNode, LDiEdge]#NodeT) =>
    getMethod(taintNode.value).call.flatMap(node =>
      operations.find { case ((name, srcIndex), _) =>
        node.name == name &&
          node.argument.argumentIndex(srcIndex).code.l.contains(getCode(taintNode.value)) &&
          taintNode.value.isSource
      }.map { case ((_, _), dstIndex) => (taintNode.value ~+> TaintNode(node.argument(dstIndex).id, TaintNodeType.Argument, isSource = true)) (EdgeType.IndirectSource) }
    )
  ).toList

def getIndirectSourceCall(nodes: Graph[TaintNode, LDiEdge]#NodeSetT, operations: Map[String, Int]): List[LDiEdge[TaintNode]] =
  nodes.flatMap((taintNode: Graph[TaintNode, LDiEdge]#NodeT) =>
    getMethod(taintNode.value).call.flatMap(node =>
      operations.find { case (name, srcIndex) => node.name == name &&
        node.argument.argumentIndex(srcIndex).code.l.contains(getCode(taintNode.value)) &&
        taintNode.value.isSource
      }.map(_ => (taintNode.value ~+> TaintNode(node.id, TaintNodeType.Call, isSource = true)) (EdgeType.IndirectSourceCall))
    )
  ).toList

def getCreatedSourceFunctions(calls: Traversal[Call], sourceCreator: Map[String, Int], sourceOperations: Map[String, Int]) =
  calls.flatMap(node =>
    sourceOperations.flatMap { case (sourceName, sourceIndex) =>
      sourceCreator.find { case (creatorName, sourceNameIndex) => node.name == creatorName &&
        // Escaping double quote doesn't work https://github.com/scala/bug/issues/6476
        node.argument.argumentIndex(sourceNameIndex).code.l.contains(s""""$sourceName"""")
      }.map(_ => (node.code, sourceIndex))
    }
  ).l.toMap

def getCastVariables(calls: Traversal[Call], creators: Map[String, Int]) =
  calls.flatMap(node =>
    creators.filter { case (name, _) =>
      node.name == "<operator>.cast" && node.argument.argumentIndex(2).code.l.contains(name)
    }.map { case (_, index) =>
      (node.code, index)
    }
  ).l.toMap

def getAssignmentVariables(calls: Traversal[Call], creators: Map[String, Int]) =
  calls.flatMap(node =>
    creators.filter { case (name, _) =>
      node.name == "<operator>.assignment" && node.argument.argumentIndex(2).code.l.contains(name)
    }.map { case (_, index) =>
      (node.argument.argumentIndex(1).code.l.head, index)
    }
  ).l.toMap

def followFunctionCalls(nodes: Graph[TaintNode, LDiEdge]#NodeSetT): List[LDiEdge[TaintNode]] =
  nodes.flatMap((taintNode: Graph[TaintNode, LDiEdge]#NodeT) =>
    getMethod(taintNode.value).call.
      filter(node => node.callee.isExternal(false).nonEmpty).
      flatMap(node =>
        node.argument.filter(arg =>
          arg.code == getCode(taintNode.value) &&
            taintNode.value.isSource
        ).flatMap(arg =>
          List(
            (taintNode.value ~+> TaintNode(arg.call.id.head, TaintNodeType.Call, isSource = false)) (EdgeType.Call),
            (TaintNode(arg.call.id.head, TaintNodeType.Call, isSource = false) ~+> TaintNode(arg.parameter.id.head, TaintNodeType.Parameter, isSource = true)) (EdgeType.Parameter)
          )
        )
      ).l
  ).toList

def findReturns(nodes: Graph[TaintNode, LDiEdge]#NodeSetT): List[LDiEdge[TaintNode]] =
  nodes.flatMap((taintNode: Graph[TaintNode, LDiEdge]#NodeT) =>
    getMethod(taintNode.value).find(method =>
      method.methodReturn.toReturn.astChildren.code.l.contains(getCode(taintNode.value)) &&
        taintNode.value.isSource
    ).map(method =>
      (taintNode.value ~+> TaintNode(method.methodReturn.toReturn.id.head, TaintNodeType.Return, isSource = false)) (EdgeType.Return)
    )
  ).toList

def followReturns(nodes: Graph[TaintNode, LDiEdge]#NodeSetT): List[LDiEdge[TaintNode]] =
  nodes.filter((taintNode: Graph[TaintNode, LDiEdge]#NodeT) =>
    taintNode.value.nodeType == TaintNodeType.Return
  ).map((taintNode: Graph[TaintNode, LDiEdge]#NodeT) =>
    (taintNode.value ~+> TaintNode(taintNode.outerNodeTraverser.
      findPredecessor(node => node.value.nodeType == TaintNodeType.Call && !node.value.isSource).get.value.id,
      TaintNodeType.Argument, isSource = true)) (EdgeType.Return)
  ).toList

def getSinks(nodes: Graph[TaintNode, LDiEdge]#NodeSetT, operations: Map[String, Int]): List[LDiEdge[TaintNode]] =
  nodes.flatMap((taintNode: Graph[TaintNode, LDiEdge]#NodeT) =>
    getMethod(taintNode.value).call.flatMap(node =>
      operations.find { case (name, srcIndex) => node.name == name &&
        node.argument.argumentIndex(srcIndex).code.l.contains(getCode(taintNode.value)) &&
        taintNode.value.nodeType != TaintNodeType.Call && taintNode.value.nodeType != TaintNodeType.Return
      }.map(_ => (taintNode.value ~+> TaintNode(node.id, TaintNodeType.Sink, isSource = false)) (EdgeType.Sink))
    )
  ).toList

var sourceCreatorCalls = getCreatedSourceFunctions(cpg_typed.call, sourceCreator, sourceOperations)
sourceCreatorCalls ++= getCastVariables(cpg_typed.call, sourceCreatorCalls)
sourceCreatorCalls ++= getAssignmentVariables(cpg_typed.call, sourceCreatorCalls)
sourceOperations ++= sourceCreatorCalls

taintGraph ++= getSource(cpg_typed.call, sourceOperations)
var lastCount = 0

while (lastCount != taintGraph.size) {
  lastCount = taintGraph.size
  taintGraph ++= getIndirectSource(taintGraph.nodes, indirectSourceOperations)
  taintGraph ++= getIndirectSourceCall(taintGraph.nodes, indirectSourceOperationsCall)
  taintGraph ++= followFunctionCalls(taintGraph.nodes)
  taintGraph ++= findReturns(taintGraph.nodes)
  taintGraph ++= followReturns(taintGraph.nodes)
}

taintGraph ++= getSinks(taintGraph.nodes, sinkOperations)

new PrintWriter("taintGraph.dot") {
  write(exportPrettyTaintGraph(taintGraph))
  close()
}
println(exportTaintGraph(taintGraph))
println()
println(s"Found ${taintGraph.nodes.size} nodes.\n")


println("Found " + taintGraph.nodes.count((taintNode: Graph[TaintNode, LDiEdge]#NodeT) => taintNode.value.nodeType == TaintNodeType.Sink) + " sink.")
