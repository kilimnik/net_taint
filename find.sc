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
  val Root, Argument, Parameter, Return, Call, Sink, Method = Value
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

def getMethod(node: TaintNode) =
  node.nodeType match {
    case TaintNodeType.Argument => getArgumentMethod(node.id)
    case TaintNodeType.Parameter => getParameterMethod(node.id)
    case TaintNodeType.Return => getReturnMethod(node.id)
    case TaintNodeType.Call => getCallMethod(node.id)
    case TaintNodeType.Method => getMethodFromId(node.id)
  }

def getCode(node: TaintNode) =
  node.nodeType match {
    case TaintNodeType.Argument => getArgumentFromId(node.id).code.head
    case TaintNodeType.Parameter => getParameterFromId(node.id).name.head
    case TaintNodeType.Return => getReturnFromId(node.id).astChildren.code.head
    case TaintNodeType.Call => getCallFromId(node.id).code.head
  }

def renderNode(innerNode: Graph[TaintNode, WLDiEdge]#NodeT, weightMap: Map[TaintNode, TaintNodeWeight]) = {
  val node = innerNode.value
  node.nodeType match {
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

  //  methodGraph ++= graph.edges
  //    .filter((innerEdge: Graph[TaintNode, WLDiEdge]#EdgeT) =>
  //      innerEdge.edge.label == EdgeType.Return
  //    )
  //    .flatMap((innerEdge: Graph[TaintNode, WLDiEdge]#EdgeT) =>
  //      List(
  //        (innerEdge.from.value ~%+> TaintNode(getMethod(innerEdge.to.value).head.id, TaintNodeType.Method, isSource = false)) (0, EdgeType.Return),
  //        (TaintNode(getMethod(innerEdge.to.value).head.id, TaintNodeType.Method, isSource = false) ~%+> innerEdge.to.value) (0, EdgeType.Call)
  //      )
  //    )

  methodGraph
}

case class OperationValue(index: Int, weight: Double = 0)

// Map[Function name, OperationValue]
var sourceOperations: Map[String, OperationValue] = Map(
  "recv" -> OperationValue(2, 1),
  "recvfrom" -> OperationValue(2, 1),
  "WSARecvEx" -> OperationValue(2, 1),
  "HttpQueryInfo" -> OperationValue(3, 1),
  "HttpQueryInfoA" -> OperationValue(3, 1),
  "HttpQueryInfoW" -> OperationValue(3, 1),
  "InternetReadFile" -> OperationValue(2, 1),
  "InternetReadFileExA" -> OperationValue(2, 1),
  "InternetReadFileExW" -> OperationValue(2, 1),
)

// Map[Function name, OperationValue]
val sinkOperations: Map[String, OperationValue] = Map(
  "atoi" -> OperationValue(1, 2),
  "_wtoi" -> OperationValue(1, 2),
  "atoi_l" -> OperationValue(1, 2),
  "_wtoi_l" -> OperationValue(1, 2),
  "strlen" -> OperationValue(1, 2),
  "strcpy" -> OperationValue(1, 2),
  "wcscpy" -> OperationValue(1, 2),
  "_mbscpy" -> OperationValue(1, 2),
  "lstrcat" -> OperationValue(1, 2),
  "lstrcatA" -> OperationValue(1, 2),
  "lstrcatW" -> OperationValue(1, 2),
  "lstrcpy" -> OperationValue(1, 2),
  "lstrcpyA" -> OperationValue(1, 2),
  "lstrcpyW" -> OperationValue(1, 2),
  "lstrcpyn" -> OperationValue(1, 2),
  "lstrcpynA" -> OperationValue(1, 2),
  "lstrcpynW" -> OperationValue(1, 2),
  "lstrlen" -> OperationValue(1, 2),
  "lstrlenA" -> OperationValue(1, 2),
  "lstrlenW" -> OperationValue(1, 2),
  "_atodbl" -> OperationValue(2, 2),
  "_atodbl_l" -> OperationValue(2, 2),
  "_atoldbl" -> OperationValue(2, 2),
  "_atoldbl_l" -> OperationValue(2, 2),
  "_atoflt" -> OperationValue(2, 2),
  "_atoflt_l" -> OperationValue(2, 2),
  "atof" -> OperationValue(1, 2),
  "_atof_l" -> OperationValue(1, 2),
  "_wtof" -> OperationValue(1, 2),
  "_wtof_l" -> OperationValue(1, 2),
  "_atoi64" -> OperationValue(1, 2),
  "_wtoi64" -> OperationValue(1, 2),
  "_atoi64_l" -> OperationValue(1, 2),
  "_wtoi64_l" -> OperationValue(1, 2),
  "atol" -> OperationValue(1, 2),
  "_atol_l" -> OperationValue(1, 2),
  "_wtol" -> OperationValue(1, 2),
  "_wtol_l" -> OperationValue(1, 2),
  "atoll" -> OperationValue(1, 2),
  "_wtoll" -> OperationValue(1, 2),
  "_atoll_l" -> OperationValue(1, 2),
  "_wtoll_l" -> OperationValue(1, 2),
  "system" -> OperationValue(1, 2),
)

// Map[Function name, Src Index, OperationValue]
val indirectSourceOperations: Map[(String, Int), OperationValue] = Map(
  ("memcpy", 2) -> OperationValue(1, 3),
  ("<operator>.assignment", 2) -> OperationValue(1, 3),
  ("strcpy", 2) -> OperationValue(1, 3),
  ("wcscpy", 2) -> OperationValue(1, 3),
  ("_mbscpy", 2) -> OperationValue(1, 3),
  ("lstrcat", 2) -> OperationValue(1, 3),
  ("lstrcatA", 2) -> OperationValue(1, 3),
  ("lstrcatW", 2) -> OperationValue(1, 3),
  ("lstrcpy", 2) -> OperationValue(1, 3),
  ("lstrcpyA", 2) -> OperationValue(1, 3),
  ("lstrcpyW", 2) -> OperationValue(1, 3),
  ("lstrcpyn", 2) -> OperationValue(1, 3),
  ("lstrcpynA", 2) -> OperationValue(1, 3),
  ("lstrcpynW", 2) -> OperationValue(1, 3),
)

// Map[Function name, OperationValue]
val indirectSourceOperationsCall: Map[String, OperationValue] = Map(
  "<operator>.indirectIndexAccess" -> OperationValue(1, 4),
  "<operator>.cast" -> OperationValue(2, 4),
  "<operator>.addition" -> OperationValue(1, 4),
  "<operator>.addressOf" -> OperationValue(1, 4),
  "<operator>.indirection" -> OperationValue(1, 4),
)

val indirectSourceHint: Map[String, OperationValue] = Map(
  "<operator>.preIncrement" -> OperationValue(1, 0.5),
  "<operator>.postIncrement" -> OperationValue(1, 0.5)
)

// Map[Function name, source name Index]
val sourceCreator: Map[String, Int] = Map(
  "GetProcAddress" -> 2
)


def getSource(calls: Traversal[Call], operations: Map[String, OperationValue]): List[WLDiEdge[TaintNode]] = {
  calls.filter(call => operations.keys.toList.contains(call.name))
    .map(node => (
      rootNode ~%+>
        TaintNode(
          node.argument.argumentIndex(operations(node.name).index).id.head,
          TaintNodeType.Argument, isSource = true
        )) (operations(node.name).weight, EdgeType.Source)).l
}


def getIndirectSource(nodes: Graph[TaintNode, WLDiEdge]#NodeSetT, operations: Map[(String, Int), OperationValue]): List[WLDiEdge[TaintNode]] =
  nodes.flatMap((taintNode: Graph[TaintNode, WLDiEdge]#NodeT) =>
    getMethod(taintNode.value).call.flatMap(node =>
      operations.find { case ((name, srcIndex), _) =>
        node.name == name &&
          node.argument.argumentIndex(srcIndex).code.l.contains(getCode(taintNode.value)) &&
          taintNode.value.isSource
      }.map { case ((_, _), operationValue: OperationValue) => (taintNode.value ~%+>
        TaintNode(
          node.argument(operationValue.index).id,
          TaintNodeType.Argument, isSource = true)
        ) (operationValue.weight, EdgeType.IndirectSource)
      }
    )
  ).toList

def getIndirectSourceCall(nodes: Graph[TaintNode, WLDiEdge]#NodeSetT, operations: Map[String, OperationValue], isSource: Boolean): List[WLDiEdge[TaintNode]] =
  nodes.flatMap((taintNode: Graph[TaintNode, WLDiEdge]#NodeT) =>
    getMethod(taintNode.value).call.flatMap(node =>
      operations.find { case (name, operationValue: OperationValue) => node.name == name &&
        node.argument.argumentIndex(operationValue.index).code.l.contains(getCode(taintNode.value)) &&
        taintNode.value.isSource
      }.map { case (_, operationValue: OperationValue) =>
        (taintNode.value ~%+> TaintNode(node.id, TaintNodeType.Call, isSource)) (operationValue.weight, EdgeType.IndirectSourceCall)
      }
    )
  ).toList

def getCreatedSourceFunctions(calls: Traversal[Call], sourceCreator: Map[String, Int], sourceOperations: Map[String, OperationValue]) =
  calls.flatMap(node =>
    sourceOperations.flatMap { case (sourceName, operationValue: OperationValue) =>
      sourceCreator.find { case (creatorName, sourceNameIndex) => node.name == creatorName &&
        // Escaping double quote doesn't work https://github.com/scala/bug/issues/6476
        node.argument.argumentIndex(sourceNameIndex).code.l.contains(s""""$sourceName"""")
      }.map(_ => (node.code, operationValue))
    }
  ).l.toMap

def getCastVariables(calls: Traversal[Call], creators: Map[String, OperationValue]) =
  calls.flatMap(node =>
    creators.filter { case (name, _) =>
      node.name == "<operator>.cast" && node.argument.argumentIndex(2).code.l.contains(name)
    }.map { case (_, operationValue) =>
      (node.code, operationValue)
    }
  ).l.toMap

def getAssignmentVariables(calls: Traversal[Call], creators: Map[String, OperationValue]) =
  calls.flatMap(node =>
    creators.filter { case (name, _) =>
      node.name == "<operator>.assignment" && node.argument.argumentIndex(2).code.l.contains(name)
    }.map { case (_, operationValue) =>
      (node.argument.argumentIndex(1).code.l.head, operationValue)
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

def getSinks(nodes: Graph[TaintNode, WLDiEdge]#NodeSetT, operations: Map[String, OperationValue]): List[WLDiEdge[TaintNode]] =
  nodes.flatMap((taintNode: Graph[TaintNode, WLDiEdge]#NodeT) =>
    getMethod(taintNode.value).call.flatMap(node =>
      operations.find { case (name, operationValue: OperationValue) => node.name == name &&
        node.argument.argumentIndex(operationValue.index).code.l.contains(getCode(taintNode.value)) &&
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
  taintGraph ++= getIndirectSourceCall(taintGraphNoRoot.nodes, indirectSourceOperationsCall, isSource = true)
  taintGraph ++= getIndirectSourceCall(taintGraphNoRoot.nodes, indirectSourceHint, isSource = false)
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
