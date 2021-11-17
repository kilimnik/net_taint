import io.shiftleft.codepropertygraph.Cpg
import io.shiftleft.codepropertygraph.generated.nodes.Call
import io.shiftleft.semanticcpg.language._
import overflowdb.traversal.Traversal
import scalax.collection.Graph
import scalax.collection.edge.Implicits.any2XEdgeAssoc
import scalax.collection.edge.WLDiEdge
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
  val Source, IndirectSource, IndirectSourceCall, Call, Parameter, Return, ReturnCall, Sink = Value
}

object TaintNodeType extends Enumeration {
  type TaintNodeType = Value
  val Root, Argument, Parameter, Return, Call, Sink, Method, Source = Value
}

import TaintNodeType._

case class TaintNode(id: Long,
                     nodeType: TaintNodeType,
                     isSource: Boolean)

case class TaintNodeWeight(var shortestPath: Double = Double.PositiveInfinity,
                           var visited: Boolean = false)

val rootNode = TaintNode(0, TaintNodeType.Root, isSource = false)
var taintGraph: Graph[TaintNode, WLDiEdge] = Graph(rootNode)
def taintGraphNoRoot = taintGraph - rootNode

var weightMap: Map[TaintNode, TaintNodeWeight] = Map(
  rootNode -> TaintNodeWeight(0)
)

var methodWeightMap: Map[TaintNode, TaintNodeWeight] = Map(
  rootNode -> TaintNodeWeight(0)
)

def getArgumentFromId(id: Long) = cpg_typed.argument.id(id)
def getArgumentMethod(id: Long) = getArgumentFromId(id).call.inAst.isMethod

def getParameterFromId(id: Long) = cpg_typed.parameter.id(id)
def getParameterMethod(id: Long) = getParameterFromId(id).method

def getReturnFromId(id: Long) = cpg_typed.ret.id(id)
def getReturnMethod(id: Long) = getReturnFromId(id).method

def getCallFromId(id: Long) = cpg_typed.call.id(id)
def getCallMethod(id: Long) = getCallFromId(id).method

def getMethodFromId(id: Long) = cpg_typed.method.id(id)

def getType(node: TaintNode) =
  cpg_typed.id(node.id).label.head match {
    case "CALL" => TaintNodeType.Call
    case "METHOD" => TaintNodeType.Method
    case "IDENTIFIER" => TaintNodeType.Argument
    case "RETURN" => TaintNodeType.Return
    case "METHOD_PARAMETER_IN" => TaintNodeType.Parameter
    case default => node.nodeType
  }

def getMethod(node: TaintNode) =
  getType(node) match {
    case TaintNodeType.Argument => getArgumentMethod(node.id)
    case TaintNodeType.Parameter => getParameterMethod(node.id)
    case TaintNodeType.Return => getReturnMethod(node.id)
    case TaintNodeType.Call => getCallMethod(node.id)
    case TaintNodeType.Method => getMethodFromId(node.id)
  }

def getCode(node: TaintNode) =
  getType(node) match {
    case TaintNodeType.Argument => getArgumentFromId(node.id).code.head
    case TaintNodeType.Parameter => getParameterFromId(node.id).name.head
    case TaintNodeType.Return => getReturnFromId(node.id).astChildren.code.head
    case TaintNodeType.Call => getCallFromId(node.id).code.head
  }

def renderNode(innerNode: Graph[TaintNode, WLDiEdge]#NodeT, weightMap: Map[TaintNode, TaintNodeWeight]) = {
  val node = innerNode.value
  getType(node) match {
    case TaintNodeType.Argument =>
      def arg = getArgumentFromId(node.id)

      s"""${weightMap.getOrElse(node, TaintNodeWeight()).shortestPath}: ${arg.call.inAst.isMethod.filename.head}#${arg.call.lineNumber.head} \n\\"${escape(arg.call.code.head)}\\" ${escape(arg.code.head)}"""
    case TaintNodeType.Parameter =>
      def param = getParameterFromId(node.id)

      s"""${weightMap.getOrElse(node, TaintNodeWeight()).shortestPath}: ${param.method.filename.head}#${param.lineNumber.head} \n\\"${escape(param.method.code.head)}\\" ${escape(param.name.head)}"""
    case TaintNodeType.Return =>
      def ret = getReturnFromId(node.id)

      s"""${weightMap.getOrElse(node, TaintNodeWeight()).shortestPath}: ${ret.method.filename.head}#${ret.lineNumber.head} \n\\"${escape(ret.code.head)}\\" ${escape(ret.astChildren.code.head)}"""
    case TaintNodeType.Call =>
      def call = getCallFromId(node.id)

      s"""${weightMap.getOrElse(node, TaintNodeWeight()).shortestPath}: ${call.method.filename.head}#${call.lineNumber.head} \n\\"${escape(call.code.head)}\\""""
    case TaintNodeType.Sink =>
      def call = getCallFromId(node.id)

      s"""${weightMap.getOrElse(node, TaintNodeWeight()).shortestPath}: ${call.method.filename.head}#${call.lineNumber.head} \n\\"${escape(call.code.head)}\\""""
    case TaintNodeType.Root => "Root"
    case TaintNodeType.Method =>
      def method = getMethodFromId(node.id)

      s"""${weightMap.getOrElse(node, TaintNodeWeight()).shortestPath}: ${method.filename.head}#${method.lineNumber.head} \n\\"${escape(method.code.head)}\\""""
  }
}

def getNodeAttrList(node: TaintNode) = {
  val attrList: ListBuffer[DotAttr] = ListBuffer()

  if (node.nodeType == TaintNodeType.Sink) {
    attrList += DotAttr(Id("shape"), Id("diamond"))
  } else if (node.nodeType == TaintNodeType.Method) {
    attrList += DotAttr(Id("shape"), Id("parallelogram"))
  } else if (node.nodeType == TaintNodeType.Source) {
    attrList += DotAttr(Id("shape"), Id("house"))
  } else if (!node.isSource) {
    attrList += DotAttr(Id("shape"), Id("plain"))
  } else {
    node.nodeType match {
      case TaintNodeType.Argument =>

      case TaintNodeType.Parameter =>

      case TaintNodeType.Return =>

      case TaintNodeType.Call =>

      case TaintNodeType.Root =>

    }
  }

  attrList.toSeq
}

def getEdgeAttrList(edge: WLDiEdge[Graph[TaintNode, WLDiEdge]#NodeT]) = {
  val attrList: ListBuffer[DotAttr] = ListBuffer()
  attrList += DotAttr(Id("label"), Id(s"${edge.weight}: ${edge.label.toString}"))
  attrList += DotAttr(Id("penwidth"), Id((edge.weight + 1).toString))

  attrList.toSeq
}

def exportPrettyTaintGraph(taintGraph: Graph[TaintNode, WLDiEdge], weightMap: Map[TaintNode, TaintNodeWeight]) = {
  val dotRoot = DotRootGraph(
    directed = true,
    id = Some(Id("TaintDot")),
    attrList = Seq(
      DotAttr(Id("nodesep"), Id("1.5")),
      DotAttr(Id("ranksep"), Id("1.5")),
    )
  )

  def edgeTransformer(innerEdge: Graph[TaintNode, WLDiEdge]#EdgeT): Option[(DotGraph, DotEdgeStmt)] = {
    val edge = innerEdge.edge
    Some(
      dotRoot,
      DotEdgeStmt(
        NodeId(renderNode(edge.from, weightMap)),
        NodeId(renderNode(edge.to, weightMap)),
        getEdgeAttrList(edge)
      )
    )
  }

  def nodeTransformer(innerNode: Graph[TaintNode, WLDiEdge]#NodeT): Option[(DotGraph, DotNodeStmt)] =
    Some(dotRoot, DotNodeStmt(NodeId(renderNode(innerNode, weightMap)), getNodeAttrList(innerNode.value)))

  taintGraph.toDot(
    dotRoot,
    edgeTransformer,
    iNodeTransformer = Some(nodeTransformer),
    cNodeTransformer = Some(nodeTransformer),
  )
}

def exportTaintGraph(taintGraph: Graph[TaintNode, WLDiEdge]) = {
  val dotRoot = DotRootGraph(
    directed = true,
    id = Some(Id("TaintDot")),
  )

  def edgeTransformer(innerEdge: Graph[TaintNode, WLDiEdge]#EdgeT): Option[(DotGraph, DotEdgeStmt)] = {
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

  def nodeTransformer(innerNode: Graph[TaintNode, WLDiEdge]#NodeT): Option[(DotGraph, DotNodeStmt)] =
    Some(dotRoot, DotNodeStmt(NodeId(innerNode.toString)))

  taintGraph.toDot(
    dotRoot,
    edgeTransformer,
    iNodeTransformer = Some(nodeTransformer)
  )
}

def fillShortestPaths(graph: Graph[TaintNode, WLDiEdge], src: TaintNode, pWeightMap: Map[TaintNode, TaintNodeWeight]): Map[TaintNode, TaintNodeWeight] = {
  var weightMap: Map[TaintNode, TaintNodeWeight] = Map()
  weightMap ++= pWeightMap

  val src_value = weightMap.getOrElse(src, TaintNodeWeight())
  src_value.visited = true
  weightMap += src -> src_value

  graph.get(src)
    .edges
    .filter(edge => edge.from.value == src)
    .filter(edge => !weightMap.getOrElse(edge.to.value, TaintNodeWeight()).visited)
    .foreach(edge => {
      val value = weightMap.getOrElse(edge.to.value, TaintNodeWeight())
      value.shortestPath = Math.min(value.shortestPath, src_value.shortestPath + edge.weight)
      weightMap += edge.to.value -> value
    })

  val new_src = graph.nodes.reduceLeft((node1: Graph[TaintNode, WLDiEdge]#NodeT, node2: Graph[TaintNode, WLDiEdge]#NodeT) => {
    val value2 = weightMap.getOrElse(node2.value, TaintNodeWeight())

    if (value2.visited) {
      node1
    } else {
      val value1 = weightMap.getOrElse(node1.value, TaintNodeWeight())
      if (value1.visited || value1.shortestPath > value2.shortestPath) {
        node2
      } else {
        node1
      }
    }
  })

  val new_src_value = weightMap.getOrElse(new_src.value, TaintNodeWeight())
  if (!new_src_value.visited) {
    weightMap ++= fillShortestPaths(graph, new_src.value, weightMap)
  }

  weightMap
}

def getMethodGraph(graph: Graph[TaintNode, WLDiEdge]) = {
  var methodGraph: Graph[TaintNode, WLDiEdge] = Graph()

  methodGraph ++= graph.edges
    .filter((innerEdge: Graph[TaintNode, WLDiEdge]#EdgeT) => innerEdge.edge.label != EdgeType.Source)
    .filter((innerEdge: Graph[TaintNode, WLDiEdge]#EdgeT) => innerEdge.edge.label != EdgeType.Parameter)
    .filter((innerEdge: Graph[TaintNode, WLDiEdge]#EdgeT) => innerEdge.edge.label != EdgeType.Return)
    .filter((innerEdge: Graph[TaintNode, WLDiEdge]#EdgeT) => innerEdge.edge.label != EdgeType.ReturnCall)

  methodGraph ++= graph.edges
    .filter((innerEdge: Graph[TaintNode, WLDiEdge]#EdgeT) => innerEdge.edge.label == EdgeType.Source)
    .flatMap((innerEdge: Graph[TaintNode, WLDiEdge]#EdgeT) =>
      List(
        (innerEdge.from.value ~%+> TaintNode(getMethod(innerEdge.to.value).head.id, TaintNodeType.Method, isSource = false)) (0, EdgeType.Call),
        (TaintNode(getMethod(innerEdge.to.value).head.id, TaintNodeType.Method, isSource = false) ~%+> innerEdge.to.value) (0, innerEdge.edge.label)
      )
    )

  methodGraph ++= graph.edges
    .filter((innerEdge: Graph[TaintNode, WLDiEdge]#EdgeT) => innerEdge.edge.label == EdgeType.Parameter)
    .flatMap((innerEdge: Graph[TaintNode, WLDiEdge]#EdgeT) =>
      List(
        (rootNode ~%+> TaintNode(getMethod(innerEdge.to.value).head.id, TaintNodeType.Method, isSource = false)) (0, EdgeType.Call),
        (TaintNode(getMethod(innerEdge.to.value).head.id, TaintNodeType.Method, isSource = false) ~%+> innerEdge.to.value) (0, innerEdge.edge.label)
      )
    )

  methodGraph ++= graph.edges
    .filter((innerEdge: Graph[TaintNode, WLDiEdge]#EdgeT) =>
      innerEdge.edge.label == EdgeType.Return
    )
    .flatMap((innerEdge: Graph[TaintNode, WLDiEdge]#EdgeT) =>
      List(
        (TaintNode(getMethod(innerEdge.to.value).head.id, TaintNodeType.Method, isSource = false) ~%+> innerEdge.to.value) (0, EdgeType.Call)
      )
    )

  methodGraph
}

case class OperationValue(weight: Double = 0)

case class Operation(name: String, srcIndex: Int = 0, dstIndex: Int = 0)

// Map[Function name, OperationValue]
var sourceOperations: Map[Operation, OperationValue] = Map(
  Operation("recv", dstIndex = 2) -> OperationValue(1),
  Operation("recvfrom", dstIndex = 2) -> OperationValue(1),
  Operation("WSARecvEx", dstIndex = 2) -> OperationValue(1),
  Operation("HttpQueryInfo", dstIndex = 3) -> OperationValue(1),
  Operation("HttpQueryInfoA", dstIndex = 3) -> OperationValue(1),
  Operation("HttpQueryInfoW", dstIndex = 3) -> OperationValue(1),
  Operation("InternetReadFile", dstIndex = 2) -> OperationValue(1),
  Operation("InternetReadFileExA", dstIndex = 2) -> OperationValue(1),
  Operation("InternetReadFileExW", dstIndex = 2) -> OperationValue(1),
)

// Map[Function name, OperationValue]
val sinkOperations: Map[Operation, OperationValue] = Map(
  Operation("atoi", srcIndex = 1) -> OperationValue(2),
  Operation("_wtoi", srcIndex = 1) -> OperationValue(2),
  Operation("atoi_l", srcIndex = 1) -> OperationValue(2),
  Operation("_wtoi_l", srcIndex = 1) -> OperationValue(2),
  Operation("strlen", srcIndex = 1) -> OperationValue(2),
  Operation("strcpy", srcIndex = 1) -> OperationValue(2),
  Operation("wcscpy", srcIndex = 1) -> OperationValue(2),
  Operation("_mbscpy", srcIndex = 1) -> OperationValue(2),
  Operation("lstrcat", srcIndex = 1) -> OperationValue(2),
  Operation("lstrcatA", srcIndex = 1) -> OperationValue(2),
  Operation("lstrcatW", srcIndex = 1) -> OperationValue(2),
  Operation("lstrcpy", srcIndex = 1) -> OperationValue(2),
  Operation("lstrcpyA", srcIndex = 1) -> OperationValue(2),
  Operation("lstrcpyW", srcIndex = 1) -> OperationValue(2),
  Operation("lstrcpyn", srcIndex = 1) -> OperationValue(2),
  Operation("lstrcpynA", srcIndex = 1) -> OperationValue(2),
  Operation("lstrcpynW", srcIndex = 1) -> OperationValue(2),
  Operation("lstrlen", srcIndex = 1) -> OperationValue(2),
  Operation("lstrlenA", srcIndex = 1) -> OperationValue(2),
  Operation("lstrlenW", srcIndex = 1) -> OperationValue(2),
  Operation("_atodbl", srcIndex = 2) -> OperationValue(2),
  Operation("_atodbl_l", srcIndex = 2) -> OperationValue(2),
  Operation("_atoldbl", srcIndex = 2) -> OperationValue(2),
  Operation("_atoldbl_l", srcIndex = 2) -> OperationValue(2),
  Operation("_atoflt", srcIndex = 2) -> OperationValue(2),
  Operation("_atoflt_l", srcIndex = 2) -> OperationValue(2),
  Operation("atof", srcIndex = 1) -> OperationValue(2),
  Operation("_atof_l", srcIndex = 1) -> OperationValue(2),
  Operation("_wtof", srcIndex = 1) -> OperationValue(2),
  Operation("_wtof_l", srcIndex = 1) -> OperationValue(2),
  Operation("_atoi64", srcIndex = 1) -> OperationValue(2),
  Operation("_wtoi64", srcIndex = 1) -> OperationValue(2),
  Operation("_atoi64_l", srcIndex = 1) -> OperationValue(2),
  Operation("_wtoi64_l", srcIndex = 1) -> OperationValue(2),
  Operation("atol", srcIndex = 1) -> OperationValue(2),
  Operation("_atol_l", srcIndex = 1) -> OperationValue(2),
  Operation("_wtol", srcIndex = 1) -> OperationValue(2),
  Operation("_wtol_l", srcIndex = 1) -> OperationValue(2),
  Operation("atoll", srcIndex = 1) -> OperationValue(2),
  Operation("_wtoll", srcIndex = 1) -> OperationValue(2),
  Operation("_atoll_l", srcIndex = 1) -> OperationValue(2),
  Operation("_wtoll_l", srcIndex = 1) -> OperationValue(2),
  Operation("system", srcIndex = 1) -> OperationValue(2),
)

// Map[Function name, Src Index, OperationValue]
val indirectSourceOperations: Map[Operation, OperationValue] = Map(
  Operation("memcpy", srcIndex = 2, dstIndex = 1) -> OperationValue(3),
  Operation("<operator>.assignment", srcIndex = 2, dstIndex = 1) -> OperationValue(3),
  Operation("<operator>.assignmentPlus", srcIndex = 2, dstIndex = 1) -> OperationValue(3),
  Operation("<operator>.assignmentMinus", srcIndex = 2, dstIndex = 1) -> OperationValue(3),
  Operation("strcpy", srcIndex = 2, dstIndex = 1) -> OperationValue(3),
  Operation("wcscpy", srcIndex = 2, dstIndex = 1) -> OperationValue(3),
  Operation("_mbscpy", srcIndex = 2, dstIndex = 1) -> OperationValue(3),
  Operation("lstrcat", srcIndex = 2, dstIndex = 1) -> OperationValue(3),
  Operation("lstrcatA", srcIndex = 2, dstIndex = 1) -> OperationValue(3),
  Operation("lstrcatW", srcIndex = 2, dstIndex = 1) -> OperationValue(3),
  Operation("lstrcpy", srcIndex = 2, dstIndex = 1) -> OperationValue(3),
  Operation("lstrcpyA", srcIndex = 2, dstIndex = 1) -> OperationValue(3),
  Operation("lstrcpyW", srcIndex = 2, dstIndex = 1) -> OperationValue(3),
  Operation("lstrcpyn", srcIndex = 2, dstIndex = 1) -> OperationValue(3),
  Operation("lstrcpynA", srcIndex = 2, dstIndex = 1) -> OperationValue(3),
  Operation("lstrcpynW", srcIndex = 2, dstIndex = 1) -> OperationValue(3),
)

// Map[Function name, OperationValue]
val indirectSourceOperationsCall: Map[Operation, OperationValue] = Map(
  Operation("<operator>.indirectIndexAccess", srcIndex = 1) -> OperationValue(4),
  Operation("<operator>.cast", srcIndex = 2) -> OperationValue(4),
  Operation("<operator>.addition", srcIndex = 1) -> OperationValue(4),
  Operation("<operator>.addressOf", srcIndex = 1) -> OperationValue(4),
  Operation("<operator>.indirection", srcIndex = 1) -> OperationValue(4),
  Operation("<operator>.preIncrement", srcIndex = 1) -> OperationValue(0.5),
  Operation("<operator>.postIncrement", srcIndex = 1) -> OperationValue(0.5),
  Operation("<operator>.notEquals", srcIndex = 1) -> OperationValue(0.5),
  Operation("<operator>.notEquals", srcIndex = 2) -> OperationValue(0.5),
  Operation("<operator>.equals", srcIndex = 1) -> OperationValue(0.5),
  Operation("<operator>.equals", srcIndex = 2) -> OperationValue(0.5),
  Operation("<operator>.lessThan", srcIndex = 1) -> OperationValue(0.5),
  Operation("<operator>.lessThan", srcIndex = 2) -> OperationValue(0.5),
  Operation("<operator>.lessEqualsThan", srcIndex = 1) -> OperationValue(0.5),
  Operation("<operator>.lessEqualsThan", srcIndex = 2) -> OperationValue(0.5),
  Operation("<operator>.greaterThan", srcIndex = 1) -> OperationValue(0.5),
  Operation("<operator>.greaterThan", srcIndex = 2) -> OperationValue(0.5),
  Operation("<operator>.greaterEqualsThan", srcIndex = 1) -> OperationValue(0.5),
  Operation("<operator>.greaterEqualsThan", srcIndex = 2) -> OperationValue(0.5),
  Operation("<operator>.logicalNot", srcIndex = 1) -> OperationValue(0.5),
  Operation("<operator>.subtraction", srcIndex = 1) -> OperationValue(0.5),
  Operation("<operator>.subtraction", srcIndex = 2) -> OperationValue(0.5),
  Operation("<operator>.addition", srcIndex = 1) -> OperationValue(0.5),
  Operation("<operator>.addition", srcIndex = 2) -> OperationValue(0.5),
)

// Map[Function name, source name Index]
val sourceCreator: Map[String, Int] = Map(
  "GetProcAddress" -> 2
)


def getSource(calls: Traversal[Call], operations: Map[Operation, OperationValue]): List[WLDiEdge[TaintNode]] =
  calls.flatMap(call =>
    operations.find { case (operation: Operation, _) =>
      operation.name == call.name
    }.map { case (operation: Operation, operationValue: OperationValue) =>
      List(
        (rootNode ~%+> TaintNode(call.id, TaintNodeType.Source, isSource = false)) (0, EdgeType.Source),
        (TaintNode(call.id, TaintNodeType.Source, isSource = false) ~%+>
          TaintNode(call.argument.argumentIndex(operation.dstIndex).id.head, TaintNodeType.Argument, isSource = true))
          (operationValue.weight, EdgeType.Call)
      )
    }
  ).l.flatten

def getIndirectSource(nodes: Graph[TaintNode, WLDiEdge]#NodeSetT, operations: Map[Operation, OperationValue]): List[WLDiEdge[TaintNode]] =
  nodes.flatMap((taintNode: Graph[TaintNode, WLDiEdge]#NodeT) =>
    getMethod(taintNode.value).call.flatMap(node =>
      operations.find { case (operation: Operation, _) =>
        node.name == operation.name &&
          node.argument.argumentIndex(operation.srcIndex).code.l.contains(getCode(taintNode.value)) &&
          taintNode.value.isSource
      }.map { case (operation: Operation, operationValue: OperationValue) => (taintNode.value ~%+>
        TaintNode(
          node.argument(operation.dstIndex).id,
          TaintNodeType.Argument, isSource = true)
        ) (operationValue.weight, EdgeType.IndirectSource)
      }
    )
  ).toList

def getIndirectSourceCall(nodes: Graph[TaintNode, WLDiEdge]#NodeSetT, operations: Map[Operation, OperationValue]): List[WLDiEdge[TaintNode]] =
  nodes.flatMap((taintNode: Graph[TaintNode, WLDiEdge]#NodeT) =>
    getMethod(taintNode.value).call.flatMap(node =>
      operations.find { case (operation: Operation, _) =>
        node.name == operation.name &&
          node.argument.argumentIndex(operation.srcIndex).code.l.contains(getCode(taintNode.value)) &&
          taintNode.value.isSource
      }.map { case (_, operationValue: OperationValue) =>
        (taintNode.value ~%+> TaintNode(node.id, TaintNodeType.Call, true)) (operationValue.weight, EdgeType.IndirectSourceCall)
      }
    )
  ).toList

def getCreatedSourceFunctions(calls: Traversal[Call], sourceCreator: Map[String, Int], sourceOperations: Map[Operation, OperationValue]) =
  calls.flatMap(node =>
    sourceOperations.flatMap { case (operation: Operation, operationValue: OperationValue) =>
      sourceCreator.find { case (creatorName, sourceNameIndex) => node.name == creatorName &&
        // Escaping double quote doesn't work https://github.com/scala/bug/issues/6476
        node.argument.argumentIndex(sourceNameIndex).code.l.contains(s""""${operation.name}"""")
      }.map(_ => (Operation(node.code, dstIndex = operation.dstIndex), operationValue))
    }
  ).l.toMap

def getCastVariables(calls: Traversal[Call], creators: Map[Operation, OperationValue]) =
  calls.flatMap(node =>
    creators.filter { case (operation, _) =>
      node.name == "<operator>.cast" && node.argument.argumentIndex(2).code.l.contains(operation.name)
    }.map { case (operation, operationValue) =>
      (Operation(node.code, dstIndex = operation.dstIndex), operationValue)
    }
  ).l.toMap

def getAssignmentVariables(calls: Traversal[Call], creators: Map[Operation, OperationValue]) =
  calls.flatMap(node =>
    creators.filter { case (operation, _) =>
      node.name == "<operator>.assignment" && node.argument.argumentIndex(2).code.l.contains(operation.name)
    }.map { case (operation, operationValue) =>
      (Operation(node.argument.argumentIndex(1).code.l.head, dstIndex = operation.dstIndex), operationValue)
    }
  ).l.toMap

def followFunctionCalls(nodes: Graph[TaintNode, WLDiEdge]#NodeSetT): List[WLDiEdge[TaintNode]] =
  nodes.flatMap((taintNode: Graph[TaintNode, WLDiEdge]#NodeT) =>
    getMethod(taintNode.value).call.
      filter(node => node.callee.isExternal(false).nonEmpty).
      flatMap(node =>
        node.argument.filter(arg =>
          arg.code == getCode(taintNode.value) &&
            taintNode.value.isSource
        ).flatMap(arg =>
          List(
            (taintNode.value ~%+> TaintNode(arg.call.id.head, TaintNodeType.Call, isSource = false)) (0, EdgeType.Call),
            (TaintNode(arg.call.id.head, TaintNodeType.Call, isSource = false) ~%+> TaintNode(arg.parameter.id.head, TaintNodeType.Parameter, isSource = true)) (0, EdgeType.Parameter)
          )
        )
      ).l
  ).toList

def findReturns(nodes: Graph[TaintNode, WLDiEdge]#NodeSetT): List[WLDiEdge[TaintNode]] =
  nodes.flatMap((taintNode: Graph[TaintNode, WLDiEdge]#NodeT) =>
    getMethod(taintNode.value).find(method =>
      method.methodReturn.toReturn.astChildren.code.l.contains(getCode(taintNode.value)) &&
        taintNode.value.isSource
    ).map(method =>
      (taintNode.value ~%+> TaintNode(method.methodReturn.toReturn.id.head, TaintNodeType.Return, isSource = false)) (0, EdgeType.ReturnCall)
    )
  ).toList

def followReturns(nodes: Graph[TaintNode, WLDiEdge]#NodeSetT): List[WLDiEdge[TaintNode]] =
  nodes.filter((taintNode: Graph[TaintNode, WLDiEdge]#NodeT) =>
    taintNode.value.nodeType == TaintNodeType.Return
  ).map((taintNode: Graph[TaintNode, WLDiEdge]#NodeT) =>
    (taintNode.value ~%+> TaintNode(taintNode.outerNodeTraverser.
      findPredecessor(node => node.value.nodeType == TaintNodeType.Call && !node.value.isSource).get.value.id,
      TaintNodeType.Argument, isSource = true)) (0, EdgeType.Return)
  ).toList

def getSinks(nodes: Graph[TaintNode, WLDiEdge]#NodeSetT, operations: Map[Operation, OperationValue]): List[WLDiEdge[TaintNode]] =
  nodes.flatMap((taintNode: Graph[TaintNode, WLDiEdge]#NodeT) =>
    getMethod(taintNode.value).call.flatMap(node =>
      operations.find { case (operation: Operation, operationValue: OperationValue) => node.name == operation.name &&
        node.argument.argumentIndex(operation.srcIndex).code.l.contains(getCode(taintNode.value)) &&
        taintNode.value.nodeType != TaintNodeType.Call && taintNode.value.nodeType != TaintNodeType.Return
      }.map { case (_, operationValue: OperationValue) =>
        (taintNode.value ~%+> TaintNode(node.id, TaintNodeType.Sink, isSource = false)) (operationValue.weight, EdgeType.Sink)
      }
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
  taintGraph ++= getIndirectSource(taintGraphNoRoot.nodes, indirectSourceOperations)
  taintGraph ++= getIndirectSourceCall(taintGraphNoRoot.nodes, indirectSourceOperationsCall)
  taintGraph ++= followFunctionCalls(taintGraphNoRoot.nodes)
  taintGraph ++= findReturns(taintGraphNoRoot.nodes)
  taintGraph ++= followReturns(taintGraphNoRoot.nodes)
}

taintGraph ++= getSinks(taintGraphNoRoot.nodes, sinkOperations)

weightMap = fillShortestPaths(taintGraph, rootNode, weightMap)

def methodGraph = getMethodGraph(taintGraph)
methodGraph.get(rootNode).diSuccessors.foreach((node: Graph[TaintNode, WLDiEdge]#NodeT) =>
  methodWeightMap += node.value -> TaintNodeWeight(
    node.innerEdgeTraverser.map((edge: Graph[TaintNode, WLDiEdge]#EdgeT) => edge.weight).sum / (getMethod(node.value).call.size + 1)
  ))

new PrintWriter("taintGraphSimple.dot") {
  write(exportTaintGraph(taintGraph))
  close()
}
new PrintWriter("taintGraph.dot") {
  write(exportPrettyTaintGraph(taintGraphNoRoot, weightMap))
  close()
}
new PrintWriter("methodGraph.dot") {
  write(exportPrettyTaintGraph(methodGraph - rootNode, methodWeightMap))
  close()
}

println()
println(s"Found ${taintGraphNoRoot.nodes.size} nodes.\n")

def sinks = taintGraphNoRoot.nodes
  .filter((taintNode: Graph[TaintNode, WLDiEdge]#NodeT) => taintNode.value.nodeType == TaintNodeType.Sink)
  .toList
  .sortWith((node1: Graph[TaintNode, WLDiEdge]#NodeT, node2: Graph[TaintNode, WLDiEdge]#NodeT) =>
    weightMap.getOrElse(node1.value, TaintNodeWeight()).shortestPath > weightMap.getOrElse(node2.value, TaintNodeWeight()).shortestPath
  )

println(s"Found ${sinks.size} sink. ${sinks.map((node: Graph[TaintNode, WLDiEdge]#NodeT) => renderNode(node, weightMap)).mkString("\n", "\n\n", "\n\n")}")

def methods = methodGraph.nodes
  .filter((taintNode: Graph[TaintNode, WLDiEdge]#NodeT) => taintNode.value.nodeType == TaintNodeType.Method)
  .toList
  .sortWith((node1: Graph[TaintNode, WLDiEdge]#NodeT, node2: Graph[TaintNode, WLDiEdge]#NodeT) =>
    methodWeightMap.getOrElse(node1.value, TaintNodeWeight()).shortestPath > methodWeightMap.getOrElse(node2.value, TaintNodeWeight()).shortestPath
  )

println(s"Found ${sinks.size} methods. ${methods.map((node: Graph[TaintNode, WLDiEdge]#NodeT) => renderNode(node, methodWeightMap)).mkString("\n", "\n\n", "\n\n")}")
