// ammonite 2.4.1

import io.shiftleft.codepropertygraph.Cpg
import io.shiftleft.codepropertygraph.generated.nodes.Call
import io.shiftleft.semanticcpg.language._
import overflowdb.traversal.Traversal
import scalax.collection.Graph
import scalax.collection.edge.Implicits.any2XEdgeAssoc
import scalax.collection.edge.WLDiEdge
import scalax.collection.io.dot._
import scala.sys.process.Process
import java.io.{File, PrintWriter}
import scala.collection.mutable.ListBuffer
import scala.reflect.io.Directory

//import $ivy.`org.scala-graph:graph-core_2.13:1.13.3`
//import $ivy.`org.scala-graph:graph-dot_2.13:1.13.0`
import $ivy.`org.scala-graph:graph-core_2.13:1.13.3`
import $ivy.`org.scala-graph:graph-dot_2.13:1.13.0`

import $ivy.`io.shiftleft:semanticcpg_2.13:1.3.381`

def cpg_typed: Cpg = cpg
def output_path = s"${project.inputPath}/out"
def directory: File = new File(output_path)
val directoryD = new Directory(directory)
directoryD.deleteRecursively()
if (!directory.exists()) {
  directory.mkdir()
}

def escape(raw: String): String = {
  import org.apache.commons.lang.StringEscapeUtils.escapeJava
  escapeJava(raw)
}

object EdgeType extends Enumeration {
  type EdgeType = Value
  val Source, IndirectSource, IndirectSourceCall, Call, Parameter,
      ParameterReverse, ParameterSource, Return, ReturnCall, Sink = Value
}

object TaintNodeType extends Enumeration {
  type TaintNodeType = Value
  val Root, Argument, Parameter, ParameterReverse, Return, Call, Sink, Method,
      Source = Value
}

import TaintNodeType._

case class TaintNode(id: Long, nodeType: TaintNodeType, isSource: Boolean)

case class TaintNodeWeight(
    var shortestPath: Double = Double.PositiveInfinity,
    var visited: Boolean = false
)

val rootNode = TaintNode(0, TaintNodeType.Root, isSource = false)
var taintGraph: Graph[TaintNode, WLDiEdge] = Graph(rootNode)
def taintGraphNoRoot = taintGraph - rootNode

var weightMap: Map[TaintNode, TaintNodeWeight] = Map(
  rootNode -> TaintNodeWeight(0)
)

var methodWeightMap: Map[TaintNode, TaintNodeWeight] = Map(
  rootNode -> TaintNodeWeight(0)
)

def getArgumentFromId(id: Long) =
  cpg_typed.argument.id(id) ++ cpg_typed.identifier.id(id)
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
    case "CALL"                => TaintNodeType.Call
    case "METHOD"              => TaintNodeType.Method
    case "IDENTIFIER"          => TaintNodeType.Argument
    case "RETURN"              => TaintNodeType.Return
    case "METHOD_PARAMETER_IN" => TaintNodeType.Parameter
    case default               => node.nodeType
  }

def getMethod(node: TaintNode) =
  getType(node) match {
    case TaintNodeType.Argument         => getArgumentMethod(node.id)
    case TaintNodeType.Parameter        => getParameterMethod(node.id)
    case TaintNodeType.ParameterReverse => getParameterMethod(node.id)
    case TaintNodeType.Return           => getReturnMethod(node.id)
    case TaintNodeType.Call             => getCallMethod(node.id)
    case TaintNodeType.Method           => getMethodFromId(node.id)
  }

def getCode(node: TaintNode) =
  getType(node) match {
    case TaintNodeType.Argument         => getArgumentFromId(node.id).code.head
    case TaintNodeType.Parameter        => getParameterFromId(node.id).name.head
    case TaintNodeType.ParameterReverse => getParameterFromId(node.id).name.head
    case TaintNodeType.Return => getReturnFromId(node.id).astChildren.code.head
    case TaintNodeType.Call   => getCallFromId(node.id).code.head
  }

def getObject(node: TaintNode) =
  getType(node) match {
    case TaintNodeType.Argument         => getArgumentFromId(node.id)
    case TaintNodeType.Parameter        => getParameterFromId(node.id)
    case TaintNodeType.ParameterReverse => getParameterFromId(node.id)
    case TaintNodeType.Return           => getReturnFromId(node.id).astChildren
    case TaintNodeType.Call             => getCallFromId(node.id)
  }

def renderNode(
    innerNode: Graph[TaintNode, WLDiEdge]#NodeT,
    weightMap: Map[TaintNode, TaintNodeWeight]
) = {
  val node = innerNode.value
  getType(node) match {
    case TaintNodeType.Argument =>
      def arg = getArgumentFromId(node.id)

      s"""${weightMap
        .getOrElse(node, TaintNodeWeight())
        .shortestPath}: ${arg.call.inAst.isMethod.filename.head}#${arg.call.lineNumber.head} \n\\"${escape(
        arg.call.code.head
      )}\\" ${escape(arg.code.head)}"""
    case TaintNodeType.Parameter =>
      def param = getParameterFromId(node.id)

      s"""${weightMap
        .getOrElse(node, TaintNodeWeight())
        .shortestPath}: ${param.method.filename.head}#${param.lineNumber.head} \n\\"${escape(
        param.method.code.head
      )}\\" ${escape(param.name.head)}"""
    case TaintNodeType.Return =>
      def ret = getReturnFromId(node.id)

      s"""${weightMap
        .getOrElse(node, TaintNodeWeight())
        .shortestPath}: ${ret.method.filename.head}#${ret.lineNumber.head} \n\\"${escape(
        ret.code.head
      )}\\" ${escape(ret.astChildren.code.head)}"""
    case TaintNodeType.Call =>
      def call = getCallFromId(node.id)

      s"""${weightMap
        .getOrElse(node, TaintNodeWeight())
        .shortestPath}: ${call.method.filename.head}#${call.lineNumber.head} \n\\"${escape(
        call.code.head
      )}\\""""
    case TaintNodeType.Sink =>
      def call = getCallFromId(node.id)

      s"""${weightMap
        .getOrElse(node, TaintNodeWeight())
        .shortestPath}: ${call.method.filename.head}#${call.lineNumber.head} \n\\"${escape(
        call.code.head
      )}\\""""
    case TaintNodeType.Root => "Root"
    case TaintNodeType.Method =>
      def method = getMethodFromId(node.id)

      s"""${weightMap
        .getOrElse(node, TaintNodeWeight())
        .shortestPath}: ${method.filename.head}#${method.lineNumber.head} \n\\"${escape(
        method.code.head
      )}\\""""
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

      case TaintNodeType.ParameterReverse =>

      case TaintNodeType.Return =>

      case TaintNodeType.Call =>

      case TaintNodeType.Root =>

    }
  }

  attrList.toSeq
}

def getEdgeAttrList(edge: WLDiEdge[Graph[TaintNode, WLDiEdge]#NodeT]) = {
  val attrList: ListBuffer[DotAttr] = ListBuffer()
  attrList += DotAttr(
    Id("label"),
    Id(s"${edge.weight}: ${edge.label.toString}")
  )
  attrList += DotAttr(Id("penwidth"), Id((edge.weight + 1).toString))

  attrList.toSeq
}

def exportPrettyTaintGraph(
    taintGraph: Graph[TaintNode, WLDiEdge],
    weightMap: Map[TaintNode, TaintNodeWeight]
) = {
  val dotRoot = DotRootGraph(
    directed = true,
    id = Some(Id("TaintDot")),
    attrList = Seq(
      DotAttr(Id("nodesep"), Id("1.5")),
      DotAttr(Id("ranksep"), Id("1.5"))
    )
  )

  def edgeTransformer(
      innerEdge: Graph[TaintNode, WLDiEdge]#EdgeT
  ): Option[(DotGraph, DotEdgeStmt)] = {
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

  def nodeTransformer(
      innerNode: Graph[TaintNode, WLDiEdge]#NodeT
  ): Option[(DotGraph, DotNodeStmt)] =
    Some(
      dotRoot,
      DotNodeStmt(
        NodeId(renderNode(innerNode, weightMap)),
        getNodeAttrList(innerNode.value)
      )
    )

  taintGraph.toDot(
    dotRoot,
    edgeTransformer,
    iNodeTransformer = Some(nodeTransformer),
    cNodeTransformer = Some(nodeTransformer)
  )
}

def exportTaintGraph(taintGraph: Graph[TaintNode, WLDiEdge]) = {
  val dotRoot = DotRootGraph(
    directed = true,
    id = Some(Id("TaintDot"))
  )

  def edgeTransformer(
      innerEdge: Graph[TaintNode, WLDiEdge]#EdgeT
  ): Option[(DotGraph, DotEdgeStmt)] = {
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

  def nodeTransformer(
      innerNode: Graph[TaintNode, WLDiEdge]#NodeT
  ): Option[(DotGraph, DotNodeStmt)] =
    Some(dotRoot, DotNodeStmt(NodeId(innerNode.toString)))

  taintGraph.toDot(
    dotRoot,
    edgeTransformer,
    iNodeTransformer = Some(nodeTransformer)
  )
}

def fillShortestPaths(
    graph: Graph[TaintNode, WLDiEdge],
    src: TaintNode,
    pWeightMap: Map[TaintNode, TaintNodeWeight]
): Map[TaintNode, TaintNodeWeight] = {
  var weightMap: Map[TaintNode, TaintNodeWeight] = Map()
  weightMap ++= pWeightMap

  val src_value = weightMap.getOrElse(src, TaintNodeWeight())
  src_value.visited = true
  weightMap += src -> src_value

  graph
    .get(src)
    .edges
    .filter(edge => edge.from.value == src)
    .filter(edge =>
      !weightMap.getOrElse(edge.to.value, TaintNodeWeight()).visited
    )
    .foreach(edge => {
      val value = weightMap.getOrElse(edge.to.value, TaintNodeWeight())
      value.shortestPath =
        Math.min(value.shortestPath, src_value.shortestPath + edge.weight)
      weightMap += edge.to.value -> value
    })

  val new_src = graph.nodes.reduceLeft(
    (
        node1: Graph[TaintNode, WLDiEdge]#NodeT,
        node2: Graph[TaintNode, WLDiEdge]#NodeT
    ) => {
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
    }
  )

  val new_src_value = weightMap.getOrElse(new_src.value, TaintNodeWeight())
  if (!new_src_value.visited) {
    weightMap ++= fillShortestPaths(graph, new_src.value, weightMap)
  }

  weightMap
}

def getMethodGraph(graph: Graph[TaintNode, WLDiEdge]) = {
  var methodGraph: Graph[TaintNode, WLDiEdge] = Graph()

  methodGraph ++= graph.edges
    .filter((innerEdge: Graph[TaintNode, WLDiEdge]#EdgeT) =>
      innerEdge.edge.label != EdgeType.Source
    )
    .filter((innerEdge: Graph[TaintNode, WLDiEdge]#EdgeT) =>
      innerEdge.edge.label != EdgeType.Parameter
    )
    .filter((innerEdge: Graph[TaintNode, WLDiEdge]#EdgeT) =>
      innerEdge.edge.label != EdgeType.ParameterReverse
    )
    .filter((innerEdge: Graph[TaintNode, WLDiEdge]#EdgeT) =>
      innerEdge.edge.label != EdgeType.ParameterSource
    )
    .filter((innerEdge: Graph[TaintNode, WLDiEdge]#EdgeT) =>
      innerEdge.edge.label != EdgeType.Return
    )
    .filter((innerEdge: Graph[TaintNode, WLDiEdge]#EdgeT) =>
      innerEdge.edge.label != EdgeType.ReturnCall
    )

  methodGraph ++= graph.edges
    .filter((innerEdge: Graph[TaintNode, WLDiEdge]#EdgeT) =>
      innerEdge.edge.label == EdgeType.Source
    )
    .flatMap((innerEdge: Graph[TaintNode, WLDiEdge]#EdgeT) =>
      List(
        (innerEdge.from.value ~%+> TaintNode(
          getMethod(innerEdge.to.value).head.id,
          TaintNodeType.Method,
          isSource = false
        ))(0, EdgeType.Call),
        (TaintNode(
          getMethod(innerEdge.to.value).head.id,
          TaintNodeType.Method,
          isSource = false
        ) ~%+> innerEdge.to.value)(0, innerEdge.edge.label)
      )
    )

  methodGraph ++= graph.edges
    .filter((innerEdge: Graph[TaintNode, WLDiEdge]#EdgeT) =>
      innerEdge.edge.label == EdgeType.Parameter
    )
    .flatMap((innerEdge: Graph[TaintNode, WLDiEdge]#EdgeT) =>
      List(
        (rootNode ~%+> TaintNode(
          getMethod(innerEdge.to.value).head.id,
          TaintNodeType.Method,
          isSource = false
        ))(0, EdgeType.Call),
        (TaintNode(
          getMethod(innerEdge.to.value).head.id,
          TaintNodeType.Method,
          isSource = false
        ) ~%+> innerEdge.to.value)(0, innerEdge.edge.label)
      )
    )

  methodGraph ++= graph.edges
    .filter((innerEdge: Graph[TaintNode, WLDiEdge]#EdgeT) =>
      innerEdge.edge.label == EdgeType.ParameterReverse
    )
    .flatMap((innerEdge: Graph[TaintNode, WLDiEdge]#EdgeT) =>
      List(
        (rootNode ~%+> TaintNode(
          getMethod(innerEdge.to.value).head.id,
          TaintNodeType.Method,
          isSource = false
        ))(0, EdgeType.Call),
        (TaintNode(
          getMethod(innerEdge.to.value).head.id,
          TaintNodeType.Method,
          isSource = false
        ) ~%+> innerEdge.to.value)(0, innerEdge.edge.label)
      )
    )

  methodGraph ++= graph.edges
    .filter((innerEdge: Graph[TaintNode, WLDiEdge]#EdgeT) =>
      innerEdge.edge.label == EdgeType.ParameterSource
    )
    .flatMap((innerEdge: Graph[TaintNode, WLDiEdge]#EdgeT) =>
      List(
        (rootNode ~%+> TaintNode(
          getMethod(innerEdge.to.value).head.id,
          TaintNodeType.Method,
          isSource = false
        ))(0, EdgeType.Call),
        (TaintNode(
          getMethod(innerEdge.to.value).head.id,
          TaintNodeType.Method,
          isSource = false
        ) ~%+> innerEdge.to.value)(0, innerEdge.edge.label)
      )
    )

  methodGraph ++= graph.edges
    .filter((innerEdge: Graph[TaintNode, WLDiEdge]#EdgeT) =>
      innerEdge.edge.label == EdgeType.Return
    )
    .flatMap((innerEdge: Graph[TaintNode, WLDiEdge]#EdgeT) =>
      List(
        (TaintNode(
          getMethod(innerEdge.to.value).head.id,
          TaintNodeType.Method,
          isSource = false
        ) ~%+> innerEdge.to.value)(0, EdgeType.Call)
      )
    )

  methodGraph
}

case class OperationValue(weight: Double = 0)

case class Operation(name: String, srcIndex: Int = 0, dstIndex: Int = 0)

val min_method_weight = 2

val recv_weight = 5
val cpy_weight = 6
val cat_weight = 7
var strlen_weight = 4
val atoi_weight = 3
val system_weight = 10
val pointer_math_weight = 5
val cmp_weight = 4

// Map[Function name, OperationValue]
var sourceOperations: Map[Operation, OperationValue] = Map(
  Operation("recv", dstIndex = 2) -> OperationValue(recv_weight),
  Operation("recvfrom", dstIndex = 2) -> OperationValue(recv_weight),
  Operation("WSARecvEx", dstIndex = 2) -> OperationValue(recv_weight),
  Operation("HttpQueryInfo", dstIndex = 3) -> OperationValue(recv_weight),
  Operation("HttpQueryInfoA", dstIndex = 3) -> OperationValue(recv_weight),
  Operation("HttpQueryInfoW", dstIndex = 3) -> OperationValue(recv_weight),
  Operation("InternetReadFile", dstIndex = 2) -> OperationValue(recv_weight),
  Operation("InternetReadFileExA", dstIndex = 2) -> OperationValue(recv_weight),
  Operation("InternetReadFileExW", dstIndex = 2) -> OperationValue(recv_weight)
)

// Map[Function name, OperationValue]
var sinkOperations: Map[Operation, OperationValue] = Map(
  Operation("strcpy", srcIndex = 1) -> OperationValue(cpy_weight),
  Operation("wcscpy", srcIndex = 1) -> OperationValue(cpy_weight),
  Operation("_mbscpy", srcIndex = 1) -> OperationValue(cpy_weight),
  Operation("lstrcpyA", srcIndex = 1) -> OperationValue(cpy_weight),
  Operation("lstrcpyW", srcIndex = 1) -> OperationValue(cpy_weight),
  Operation("lstrcpyn", srcIndex = 1) -> OperationValue(cpy_weight),
  Operation("lstrcpynA", srcIndex = 1) -> OperationValue(cpy_weight),
  Operation("lstrcpynW", srcIndex = 1) -> OperationValue(cpy_weight),
  Operation("lstrcpy", srcIndex = 1) -> OperationValue(cpy_weight),
  Operation("lstrcat", srcIndex = 1) -> OperationValue(cat_weight),
  Operation("lstrcatA", srcIndex = 1) -> OperationValue(cat_weight),
  Operation("lstrcatW", srcIndex = 1) -> OperationValue(cat_weight),
  Operation("strlen", srcIndex = 1) -> OperationValue(strlen_weight),
  Operation("lstrlen", srcIndex = 1) -> OperationValue(strlen_weight),
  Operation("lstrlenA", srcIndex = 1) -> OperationValue(strlen_weight),
  Operation("lstrlenW", srcIndex = 1) -> OperationValue(strlen_weight),
  Operation("atoi", srcIndex = 1) -> OperationValue(atoi_weight),
  Operation("_wtoi", srcIndex = 1) -> OperationValue(atoi_weight),
  Operation("atoi_l", srcIndex = 1) -> OperationValue(atoi_weight),
  Operation("_wtoi_l", srcIndex = 1) -> OperationValue(atoi_weight),
  Operation("_atodbl", srcIndex = 2) -> OperationValue(atoi_weight),
  Operation("_atodbl_l", srcIndex = 2) -> OperationValue(atoi_weight),
  Operation("_atoldbl", srcIndex = 2) -> OperationValue(atoi_weight),
  Operation("_atoldbl_l", srcIndex = 2) -> OperationValue(atoi_weight),
  Operation("_atoflt", srcIndex = 2) -> OperationValue(atoi_weight),
  Operation("_atoflt_l", srcIndex = 2) -> OperationValue(atoi_weight),
  Operation("atof", srcIndex = 1) -> OperationValue(atoi_weight),
  Operation("_atof_l", srcIndex = 1) -> OperationValue(atoi_weight),
  Operation("_wtof", srcIndex = 1) -> OperationValue(atoi_weight),
  Operation("_wtof_l", srcIndex = 1) -> OperationValue(atoi_weight),
  Operation("_atoi64", srcIndex = 1) -> OperationValue(atoi_weight),
  Operation("_wtoi64", srcIndex = 1) -> OperationValue(atoi_weight),
  Operation("_atoi64_l", srcIndex = 1) -> OperationValue(atoi_weight),
  Operation("_wtoi64_l", srcIndex = 1) -> OperationValue(atoi_weight),
  Operation("atol", srcIndex = 1) -> OperationValue(atoi_weight),
  Operation("_atol_l", srcIndex = 1) -> OperationValue(atoi_weight),
  Operation("_wtol", srcIndex = 1) -> OperationValue(atoi_weight),
  Operation("_wtol_l", srcIndex = 1) -> OperationValue(atoi_weight),
  Operation("atoll", srcIndex = 1) -> OperationValue(atoi_weight),
  Operation("_wtoll", srcIndex = 1) -> OperationValue(atoi_weight),
  Operation("_atoll_l", srcIndex = 1) -> OperationValue(atoi_weight),
  Operation("_wtoll_l", srcIndex = 1) -> OperationValue(atoi_weight),
  Operation("system", srcIndex = 1) -> OperationValue(system_weight)
)

// Map[Function name, Src Index, OperationValue]
var indirectSourceOperations: Map[Operation, OperationValue] = Map(
  Operation(
    "<operator>.assignment",
    srcIndex = 2,
    dstIndex = 1
  ) -> OperationValue(0),
  Operation(
    "<operator>.assignmentPlus",
    srcIndex = 2,
    dstIndex = 1
  ) -> OperationValue(pointer_math_weight),
  Operation(
    "<operator>.assignmentMinus",
    srcIndex = 2,
    dstIndex = 1
  ) -> OperationValue(pointer_math_weight),
  Operation("memcpy", srcIndex = 2, dstIndex = 1) -> OperationValue(cpy_weight),
  Operation("strcpy", srcIndex = 2, dstIndex = 1) -> OperationValue(cpy_weight),
  Operation("wcscpy", srcIndex = 2, dstIndex = 1) -> OperationValue(cpy_weight),
  Operation("_mbscpy", srcIndex = 2, dstIndex = 1) -> OperationValue(
    cpy_weight
  ),
  Operation("lstrcpy", srcIndex = 2, dstIndex = 1) -> OperationValue(
    cpy_weight
  ),
  Operation("lstrcpyA", srcIndex = 2, dstIndex = 1) -> OperationValue(
    cpy_weight
  ),
  Operation("lstrcpyW", srcIndex = 2, dstIndex = 1) -> OperationValue(
    cpy_weight
  ),
  Operation("lstrcpyn", srcIndex = 2, dstIndex = 1) -> OperationValue(
    cpy_weight
  ),
  Operation("lstrcpynA", srcIndex = 2, dstIndex = 1) -> OperationValue(
    cpy_weight
  ),
  Operation("lstrcpynW", srcIndex = 2, dstIndex = 1) -> OperationValue(
    cpy_weight
  ),
  Operation("lstrcat", srcIndex = 2, dstIndex = 1) -> OperationValue(
    cat_weight
  ),
  Operation("lstrcatA", srcIndex = 2, dstIndex = 1) -> OperationValue(
    cat_weight
  ),
  Operation("lstrcatW", srcIndex = 2, dstIndex = 1) -> OperationValue(
    cat_weight
  )
)

// Map[Function name, OperationValue]
var indirectSourceOperationsCall: Map[Operation, OperationValue] = Map(
  Operation("<operator>.cast", srcIndex = 1) -> OperationValue(0),
  Operation("<operator>.cast", srcIndex = 2) -> OperationValue(0),
  Operation("<operator>.indirectIndexAccess", srcIndex = 1) -> OperationValue(
    pointer_math_weight
  ),
  Operation("<operator>.addition", srcIndex = 1) -> OperationValue(
    pointer_math_weight
  ),
  Operation("<operator>.addressOf", srcIndex = 1) -> OperationValue(
    pointer_math_weight
  ),
  Operation("<operator>.indirection", srcIndex = 1) -> OperationValue(
    pointer_math_weight
  ),
  Operation("<operator>.preIncrement", srcIndex = 1) -> OperationValue(
    pointer_math_weight
  ),
  Operation("<operator>.postIncrement", srcIndex = 1) -> OperationValue(
    pointer_math_weight
  ),
  Operation("<operator>.notEquals", srcIndex = 1) -> OperationValue(cmp_weight),
  Operation("<operator>.notEquals", srcIndex = 2) -> OperationValue(cmp_weight),
  Operation("<operator>.equals", srcIndex = 1) -> OperationValue(cmp_weight),
  Operation("<operator>.equals", srcIndex = 2) -> OperationValue(cmp_weight),
  Operation("<operator>.lessThan", srcIndex = 1) -> OperationValue(cmp_weight),
  Operation("<operator>.lessThan", srcIndex = 2) -> OperationValue(cmp_weight),
  Operation("<operator>.lessEqualsThan", srcIndex = 1) -> OperationValue(
    cmp_weight
  ),
  Operation("<operator>.lessEqualsThan", srcIndex = 2) -> OperationValue(
    cmp_weight
  ),
  Operation("<operator>.greaterThan", srcIndex = 1) -> OperationValue(
    cmp_weight
  ),
  Operation("<operator>.greaterThan", srcIndex = 2) -> OperationValue(
    cmp_weight
  ),
  Operation("<operator>.greaterEqualsThan", srcIndex = 1) -> OperationValue(
    cmp_weight
  ),
  Operation("<operator>.greaterEqualsThan", srcIndex = 2) -> OperationValue(
    cmp_weight
  ),
  Operation("<operator>.logicalNot", srcIndex = 1) -> OperationValue(
    cmp_weight
  ),
  Operation("<operator>.subtraction", srcIndex = 1) -> OperationValue(
    pointer_math_weight
  ),
  Operation("<operator>.subtraction", srcIndex = 2) -> OperationValue(
    pointer_math_weight
  ),
  Operation("<operator>.addition", srcIndex = 1) -> OperationValue(
    pointer_math_weight
  ),
  Operation("<operator>.addition", srcIndex = 2) -> OperationValue(
    pointer_math_weight
  ),
  Operation("<operator>.fieldAccess", srcIndex = 1) -> OperationValue(0),
  Operation("<operator>.indirectFieldAccess", srcIndex = 1) -> OperationValue(0)
)

// Map[Function name, source name Index]
val sourceCreator: Map[String, Int] = Map(
  "GetProcAddress" -> 2
)

var subSourceCall: Map[Operation, OperationValue] = Map(
  Operation("<operator>.cast") -> OperationValue(0),
  Operation("<operator>.cast") -> OperationValue(0),
  Operation("<operator>.indirectIndexAccess") -> OperationValue(
    pointer_math_weight
  ),
  Operation("<operator>.addition") -> OperationValue(pointer_math_weight),
  Operation("<operator>.addressOf") -> OperationValue(pointer_math_weight),
  Operation("<operator>.indirection") -> OperationValue(pointer_math_weight),
  Operation("<operator>.preIncrement") -> OperationValue(pointer_math_weight),
  Operation("<operator>.postIncrement") -> OperationValue(pointer_math_weight),
  Operation("<operator>.subtraction") -> OperationValue(pointer_math_weight),
  Operation("<operator>.subtraction") -> OperationValue(pointer_math_weight),
  Operation("<operator>.addition") -> OperationValue(pointer_math_weight),
  Operation("<operator>.addition") -> OperationValue(pointer_math_weight),
  Operation("<operator>.fieldAccess") -> OperationValue(0),
  Operation("<operator>.indirectFieldAccess") -> OperationValue(0)
)

def getSource(
    calls: Traversal[Call],
    operations: Map[Operation, OperationValue]
): List[WLDiEdge[TaintNode]] =
  calls
    .flatMap(call =>
      operations
        .find { case (operation: Operation, _) =>
          operation.name == call.name || s"*${operation.name}" == call.name
        }
        .map { case (operation: Operation, operationValue: OperationValue) =>
          call.argument
            .argumentIndex(operation.dstIndex)
            .flatMap(arg =>
              List(
                (rootNode ~%+> TaintNode(
                  call.id,
                  TaintNodeType.Source,
                  isSource = false
                ))(0, EdgeType.Source),
                (TaintNode(call.id, TaintNodeType.Source, isSource = false) ~%+>
                  TaintNode(
                    call.argument.argumentIndex(operation.dstIndex).id.head,
                    TaintNodeType.Argument,
                    isSource = true
                  ))(operationValue.weight, EdgeType.Call)
              )
            )
        }
    )
    .l
    .flatten

def getIndirectSource(
    nodes: Graph[TaintNode, WLDiEdge]#NodeSetT,
    operations: Map[Operation, OperationValue]
): List[WLDiEdge[TaintNode]] =
  nodes
    .flatMap((taintNode: Graph[TaintNode, WLDiEdge]#NodeT) =>
      getMethod(taintNode.value).call.flatMap(node =>
        operations
          .find { case (operation: Operation, _) =>
            node.name == operation.name &&
              node.argument
                .argumentIndex(operation.srcIndex)
                .code
                .l
                .contains(getCode(taintNode.value)) &&
              taintNode.value.isSource
          }
          .map { case (operation: Operation, operationValue: OperationValue) =>
            (taintNode.value ~%+>
              TaintNode(
                node.argument(operation.dstIndex).id,
                TaintNodeType.Argument,
                isSource = true
              ))(operationValue.weight, EdgeType.IndirectSource)
          }
      )
    )
    .toList

def getIndirectSourceCall(
    nodes: Graph[TaintNode, WLDiEdge]#NodeSetT,
    operations: Map[Operation, OperationValue]
): List[WLDiEdge[TaintNode]] =
  nodes
    .flatMap((taintNode: Graph[TaintNode, WLDiEdge]#NodeT) =>
      getMethod(taintNode.value).call.flatMap(node =>
        operations
          .find { case (operation: Operation, _) =>
            node.name == operation.name &&
              node.argument
                .argumentIndex(operation.srcIndex)
                .code
                .l
                .contains(getCode(taintNode.value)) &&
              taintNode.value.isSource
          }
          .map { case (_, operationValue: OperationValue) =>
            (taintNode.value ~%+> TaintNode(
              node.id,
              TaintNodeType.Call,
              isSource = true
            ))(operationValue.weight, EdgeType.IndirectSourceCall)
          }
      )
    )
    .toList

def followSubSource(
    nodes: Graph[TaintNode, WLDiEdge]#NodeSetT,
    operations: Map[Operation, OperationValue]
): List[WLDiEdge[TaintNode]] =
  nodes
    .filter((taintNode: Graph[TaintNode, WLDiEdge]#NodeT) =>
      getType(taintNode.value) == TaintNodeType.Call
    )
    .flatMap((taintNode: Graph[TaintNode, WLDiEdge]#NodeT) =>
      operations
        .find { case (operation: Operation, _) =>
          getCallFromId(taintNode.value.id).name.head == operation.name
        }
        .map { case (_, operationValue: OperationValue) =>
          getCallFromId(taintNode.value.id).argument
            .filterNot(arg => arg.isLiteral)
            .map(arg =>
              (taintNode.value ~%+> TaintNode(
                arg.id,
                TaintNodeType.Argument,
                isSource = true
              ))(operationValue.weight, EdgeType.IndirectSourceCall)
            )
            .l
        }
    )
    .flatten
    .toList

def getCreatedSourceFunctions(
    calls: Traversal[Call],
    sourceCreator: Map[String, Int],
    sourceOperations: Map[Operation, OperationValue]
): Map[Operation, OperationValue] =
  calls
    .flatMap(node =>
      sourceOperations.flatMap {
        case (operation: Operation, operationValue: OperationValue) =>
          sourceCreator
            .find { case (creatorName, sourceNameIndex) =>
              node.name == creatorName &&
                // Escaping double quote doesn't work https://github.com/scala/bug/issues/6476
                (
                  node.argument
                    .argumentIndex(sourceNameIndex)
                    .code
                    .l
                    .contains(s""""${operation.name}"""") ||
                    node.code.contains(operation.name)
                )
            }
            .map(_ =>
              (
                Operation(node.code, dstIndex = operation.dstIndex),
                operationValue
              )
            )
      }
    )
    .l
    .toMap

def getCastVariables(
    calls: Traversal[Call],
    creators: Map[Operation, OperationValue]
) =
  calls
    .flatMap(node =>
      creators
        .filter { case (operation, _) =>
          node.name == "<operator>.cast" && node.argument
            .argumentIndex(2)
            .code
            .l
            .contains(operation.name)
        }
        .map { case (operation, operationValue) =>
          (Operation(node.code, dstIndex = operation.dstIndex), operationValue)
        }
    )
    .l
    .toMap

def getAssignmentVariables(
    calls: Traversal[Call],
    creators: Map[Operation, OperationValue]
): Map[Operation, OperationValue] =
  calls
    .flatMap(node =>
      creators
        .filter { case (operation, _) =>
          node.name == "<operator>.assignment" && node.argument
            .argumentIndex(2)
            .code
            .l
            .contains(operation.name)
        }
        .map { case (operation, operationValue) =>
          (
            Operation(
              node.argument.argumentIndex(1).code.l.head,
              dstIndex = operation.dstIndex
            ),
            operationValue
          )
        }
    )
    .l
    .toMap

def followFunctionCalls(
    nodes: Graph[TaintNode, WLDiEdge]#NodeSetT
): List[WLDiEdge[TaintNode]] =
  nodes
    .flatMap((taintNode: Graph[TaintNode, WLDiEdge]#NodeT) =>
      getMethod(taintNode.value).call
        .filter(node => node.callee.isExternal(false).nonEmpty)
        .flatMap(node =>
          node.argument
            .filter(arg =>
              arg.code == getCode(taintNode.value) &&
                taintNode.value.isSource &&
                !nodes.exists((paramNode: Graph[TaintNode, WLDiEdge]#NodeT) =>
                  paramNode.value.id == arg.id
                )
            )
            .flatMap(arg =>
              if (arg.parameter.size > 0)
                List(
                  (taintNode.value ~%+> TaintNode(
                    arg.call.id.head,
                    TaintNodeType.Call,
                    isSource = false
                  ))(0, EdgeType.Call),
                  (TaintNode(
                    arg.call.id.head,
                    TaintNodeType.Call,
                    isSource = false
                  ) ~%+> TaintNode(
                    arg.parameter.id.head,
                    TaintNodeType.Parameter,
                    isSource = true
                  ))(0, EdgeType.Parameter)
                )
              else List()
            )
        )
        .l
    )
    .toList

def findReturns(
    nodes: Graph[TaintNode, WLDiEdge]#NodeSetT
): List[WLDiEdge[TaintNode]] =
  nodes
    .flatMap((taintNode: Graph[TaintNode, WLDiEdge]#NodeT) =>
      getMethod(taintNode.value)
        .find(method =>
          method.methodReturn.toReturn.astChildren.code.l
            .contains(getCode(taintNode.value)) &&
            taintNode.value.isSource
        )
        .map(method =>
          (taintNode.value ~%+> TaintNode(
            method.methodReturn.toReturn.id.head,
            TaintNodeType.Return,
            isSource = false
          ))(0, EdgeType.ReturnCall)
        )
    )
    .toList

def followReturns(
    nodes: Graph[TaintNode, WLDiEdge]#NodeSetT
): List[WLDiEdge[TaintNode]] =
  nodes
    .filter((taintNode: Graph[TaintNode, WLDiEdge]#NodeT) =>
      taintNode.value.nodeType == TaintNodeType.Return
    )
    .flatMap((taintNode: Graph[TaintNode, WLDiEdge]#NodeT) =>
      taintNode.outerNodeTraverser
        .findPredecessor(node =>
          node.value.nodeType == TaintNodeType.Call && !node.value.isSource
        )
        .map(n =>
          (taintNode.value ~%+> TaintNode(
            n.value.id,
            TaintNodeType.Argument,
            isSource = true
          ))(0, EdgeType.Return)
        )
    )
    .toList

def lookForParameters(
    nodes: Graph[TaintNode, WLDiEdge]#NodeSetT
): List[WLDiEdge[TaintNode]] =
  nodes
    .filter((taintNode: Graph[TaintNode, WLDiEdge]#NodeT) =>
      taintNode.value.nodeType != TaintNodeType.ParameterReverse &&
        taintNode.value.nodeType != TaintNodeType.Parameter
    )
    .flatMap((taintNode: Graph[TaintNode, WLDiEdge]#NodeT) =>
      getMethod(taintNode.value).parameter
        .find(param =>
          param.name == getCode(taintNode.value) &&
            !nodes.exists((paramNode: Graph[TaintNode, WLDiEdge]#NodeT) =>
              paramNode.value.id == param.id
            )
        )
        .map(param =>
          (taintNode.value ~%+> TaintNode(
            param.id,
            TaintNodeType.ParameterReverse,
            isSource = true
          ))(0, EdgeType.ParameterReverse)
        )
    )
    .toList

def lookForCalls(
    nodes: Graph[TaintNode, WLDiEdge]#NodeSetT
): List[WLDiEdge[TaintNode]] =
  nodes
    .filter((taintNode: Graph[TaintNode, WLDiEdge]#NodeT) =>
      taintNode.value.nodeType == TaintNodeType.ParameterReverse
    )
    .flatMap((taintNode: Graph[TaintNode, WLDiEdge]#NodeT) =>
      getMethod(taintNode.value).callIn.flatMap(call =>
        if (
          call.argument.size > getParameterFromId(taintNode.value.id).order.head
        )
          List(
            (taintNode.value ~%+>
              TaintNode(
                call.argument
                  .argumentIndex(
                    getParameterFromId(taintNode.value.id).order.head
                  )
                  .id
                  .head,
                TaintNodeType.Argument,
                isSource = true
              ))(0, EdgeType.ParameterSource)
          )
        else List()
      )
    )
    .toList

def unzipFieldAccess(
    nodes: Graph[TaintNode, WLDiEdge]#NodeSetT
): List[WLDiEdge[TaintNode]] =
  nodes
    .filter((taintNode: Graph[TaintNode, WLDiEdge]#NodeT) =>
      getObject(taintNode.value).isCall.name.l
        .contains("<operator>.fieldAccess") || getObject(
        taintNode.value
      ).isCall.name.l.contains("<operator>.indirectFieldAccess")
    )
    .map((taintNode: Graph[TaintNode, WLDiEdge]#NodeT) =>
      (taintNode.value
        ~%+> TaintNode(
          getObject(taintNode.value).isCall.argument.argumentIndex(1).id.head,
          TaintNodeType.Argument,
          isSource = true
        ))(0, EdgeType.IndirectSource)
    )
    .toList

def getSinks(
    nodes: Graph[TaintNode, WLDiEdge]#NodeSetT,
    operations: Map[Operation, OperationValue]
): List[WLDiEdge[TaintNode]] =
  nodes
    .flatMap((taintNode: Graph[TaintNode, WLDiEdge]#NodeT) =>
      getMethod(taintNode.value).call.flatMap(node =>
        operations
          .find { case (operation: Operation, _) =>
            node.name == operation.name &&
              node.argument
                .argumentIndex(operation.srcIndex)
                .code
                .l
                .contains(getCode(taintNode.value)) &&
              taintNode.value.nodeType != TaintNodeType.Call && taintNode.value.nodeType != TaintNodeType.Return
          }
          .map { case (_, operationValue: OperationValue) =>
            (taintNode.value ~%+> TaintNode(
              node.id,
              TaintNodeType.Sink,
              isSource = false
            ))(operationValue.weight, EdgeType.Sink)
          }
      )
    )
    .toList

def search_created_functions(pOperations: Map[Operation, OperationValue]) = {
  var operations =
    collection.mutable.Map[Operation, OperationValue]() ++= pOperations

  operations.foreach { case (operation, value) =>
    var graph: Graph[TaintNode, WLDiEdge] = Graph()

    var currentOperationMap = Map[Operation, OperationValue]()
    currentOperationMap += (operation -> value)

    graph ++= cpg_typed.call
      .filter(node => getCallFromId(node.id).name.head == operation.name)
      .map(call => call.id)
      .l
      .map(id =>
        TaintNode(
          id,
          TaintNodeType.Source,
          isSource = true
        )
      )

    graph ++= cpg_typed.identifier
      .filter(node => node.code == operation.name)
      .map(node => node.id)
      .l
      .map(id =>
        TaintNode(
          id,
          TaintNodeType.Source,
          isSource = true
        )
      )

    var creatorCalls = getCreatedSourceFunctions(
      cpg_typed.call,
      sourceCreator,
      currentOperationMap
    )

    graph ++= creatorCalls.map({ case (operationInner, _) =>
      TaintNode(
        cpg_typed.call.find(node => node.code == operationInner.name).get.id,
        TaintNodeType.Source,
        isSource = true
      )
    })

    var lastCount = 0
    while (lastCount != graph.size) {
      lastCount = graph.size
      println(s"last count: ${lastCount}")

      graph ++= getIndirectSource(
        graph.nodes,
        indirectSourceOperations
      )
      graph ++= getIndirectSourceCall(
        graph.nodes,
        indirectSourceOperationsCall
      )
      graph ++= followSubSource(graph.nodes, subSourceCall)
      graph ++= followFunctionCalls(graph.nodes)
      graph ++= unzipFieldAccess(graph.nodes)
      graph ++= findReturns(graph.nodes)
      graph ++= followReturns(graph.nodes)
      graph ++= lookForParameters(graph.nodes)
      graph ++= lookForCalls(graph.nodes)
    }

    operations ++= graph.nodes
      .map((node: Graph[TaintNode, WLDiEdge]#NodeT) =>
        (
          (Operation(
            getCode(node.value),
            srcIndex = operation.srcIndex,
            dstIndex = operation.dstIndex
          )),
          value
        )
      )
      .toMap
  }

  println(operations.size)
  operations.toMap
}

println("Search sourceOperations")
sourceOperations = search_created_functions(sourceOperations)

taintGraph ++= getSource(cpg_typed.call, sourceOperations)
if (taintGraph.size == 1) {
  new PrintWriter(s"${output_path}/vuln.txt") {
    write("No sources found!")
    close()
  }

  throw new RuntimeException("No sources found!")
}

println("Search sinkOperations")
sinkOperations = search_created_functions(sinkOperations)
println("Search indirectSourceOperations")
indirectSourceOperations = search_created_functions(indirectSourceOperations)
println("Search indirectSourceOperationsCall")
indirectSourceOperationsCall = search_created_functions(
  indirectSourceOperationsCall
)
println("Search subSourceCall")
subSourceCall = search_created_functions(subSourceCall)

println("Tainting")
var lastCount = 0
while (lastCount != taintGraph.size) {
  lastCount = taintGraph.size
  println(s"last count: ${lastCount}")

  taintGraph ++= getIndirectSource(
    taintGraphNoRoot.nodes,
    indirectSourceOperations
  )
  taintGraph ++= getIndirectSourceCall(
    taintGraphNoRoot.nodes,
    indirectSourceOperationsCall
  )
  taintGraph ++= followSubSource(taintGraphNoRoot.nodes, subSourceCall)
  taintGraph ++= followFunctionCalls(taintGraphNoRoot.nodes)
  taintGraph ++= unzipFieldAccess(taintGraphNoRoot.nodes)
  taintGraph ++= findReturns(taintGraphNoRoot.nodes)
  taintGraph ++= followReturns(taintGraphNoRoot.nodes)
  taintGraph ++= lookForParameters(taintGraphNoRoot.nodes)
  taintGraph ++= lookForCalls(taintGraphNoRoot.nodes)
}

taintGraph ++= getSinks(taintGraphNoRoot.nodes, sinkOperations)

weightMap = fillShortestPaths(taintGraph, rootNode, weightMap)

new PrintWriter(s"${output_path}/taintGraphSimple.dot") {
  write(exportTaintGraph(taintGraph))
  close()
}
// Process(s"dot -Tpdf ${output_path}/taintGraphSimple.dot -o ${output_path}/taintGraphSimple.pdf").!

new PrintWriter(s"${output_path}/taintGraph.dot") {
  write(exportPrettyTaintGraph(taintGraphNoRoot, weightMap))
  close()
}
// Process(s"dot -Tpdf ${output_path}/taintGraph.dot -o ${output_path}/taintGraph.pdf").!

def methodGraph = getMethodGraph(taintGraph)
methodGraph
  .get(rootNode)
  .diSuccessors
  .foreach((node: Graph[TaintNode, WLDiEdge]#NodeT) =>
    methodWeightMap += node.value -> TaintNodeWeight(
      node.innerEdgeTraverser
        .map((edge: Graph[TaintNode, WLDiEdge]#EdgeT) => edge.weight)
        .sum / (getMethod(node.value).call.size + 1)
    )
  )

new PrintWriter(s"${output_path}/methodGraph.dot") {
  write(exportPrettyTaintGraph(methodGraph - rootNode, methodWeightMap))
  close()
}
// Process(s"dot -Tpdf ${output_path}/methodGraph.dot -o ${output_path}/methodGraph.pdf").!

var output = ""
output += s"Found ${taintGraphNoRoot.nodes.size} nodes.\n"

def sinks = taintGraphNoRoot.nodes
  .filter((taintNode: Graph[TaintNode, WLDiEdge]#NodeT) =>
    taintNode.value.nodeType == TaintNodeType.Sink
  )
  .toList
  .sortWith(
    (
        node1: Graph[TaintNode, WLDiEdge]#NodeT,
        node2: Graph[TaintNode, WLDiEdge]#NodeT
    ) =>
      weightMap
        .getOrElse(node1.value, TaintNodeWeight())
        .shortestPath > weightMap
        .getOrElse(node2.value, TaintNodeWeight())
        .shortestPath
  )

output += s"Found ${sinks.size} sink. ${sinks
  .map((node: Graph[TaintNode, WLDiEdge]#NodeT) => renderNode(node, weightMap))
  .mkString("\n", "\n\n", "\n\n")}"

def methods = methodGraph.nodes
  .filter((taintNode: Graph[TaintNode, WLDiEdge]#NodeT) =>
    taintNode.value.nodeType == TaintNodeType.Method
  )
  .toList
  .sortWith(
    (
        node1: Graph[TaintNode, WLDiEdge]#NodeT,
        node2: Graph[TaintNode, WLDiEdge]#NodeT
    ) =>
      methodWeightMap
        .getOrElse(node1.value, TaintNodeWeight())
        .shortestPath > methodWeightMap
        .getOrElse(node2.value, TaintNodeWeight())
        .shortestPath
  )

output += s"Found ${methods.size} methods. ${methods
  .map((node: Graph[TaintNode, WLDiEdge]#NodeT) => renderNode(node, methodWeightMap))
  .mkString("\n", "\n\n", "\n\n")}"
// println(output)

new PrintWriter(s"${output_path}/out.txt") {
  write(output)
  close()
}

def methods_filtered =
  methods.filter((node: Graph[TaintNode, WLDiEdge]#NodeT) =>
    methodWeightMap
      .getOrElse(node.value, TaintNodeWeight())
      .shortestPath >= min_method_weight
  )
var vuln_output = ""
vuln_output += s"Found ${sinks.size} sink. ${sinks
  .map((node: Graph[TaintNode, WLDiEdge]#NodeT) => renderNode(node, weightMap))
  .mkString("\n", "\n\n", "\n\n\n")}"

vuln_output += s"Found ${methods_filtered.size} methods. ${methods_filtered
  .map((node: Graph[TaintNode, WLDiEdge]#NodeT) => renderNode(node, methodWeightMap))
  .mkString("\n", "\n\n", "\n")}"

new PrintWriter(s"${output_path}/vuln.txt") {
  write(vuln_output)
  close()
}
