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

val DEBUG = true

def debug_graph(graph: Graph[TaintNode, WLDiEdge]) =
  if (DEBUG) {
    println(s"[DEBUG] [GRAPH_SIZE]: ${graph.nodes.size}")
  }

def time[R](block: => R, name: String): R =
  if (DEBUG) {
    val t1 = System.nanoTime
    val result = block // call-by-name

    val duration = (System.nanoTime - t1) / 1e9d
    println(s"[TIME] [${name}]: took ${duration} seconds")

    result
  } else {
    block // call-by-name
  }

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

case class TaintNode(
    id: Long,
    nodeType: TaintNodeType,
    isSource: Boolean,
    code: String
) {
  def this(id: Long, nodeType: TaintNodeType, isSource: Boolean) =
    this(id, nodeType, isSource, getCodeFromId(id, nodeType))
}

case class TaintNodeWeight(
    var shortestPath: Double = Double.PositiveInfinity,
    var visited: Boolean = false
)

object TaintFunctionType extends Enumeration {
  type TaintFunctionType = Value
  val GetIndirectSource, GetIndirectSourceCall, FollowSubSource,
      FollowFunctionCalls, UnzipFieldAccess, FindReturns, LookForParameters,
      LookForParameterCalls, LookForReturnCalls, FollowReturns = Value
}

val rootNode = TaintNode(0, TaintNodeType.Root, isSource = false, "ROOT")
var taintGraph: Graph[TaintNode, WLDiEdge] = Graph(rootNode)
def taintGraphNoRoot = taintGraph - rootNode
var taintIds: Map[Long, Boolean] = Map()

def clear_caches() = {
  taintIds = Map()
}

def addTaintSourceIdsFromEdge(
    block: => List[WLDiEdge[TaintNode]],
    taintFunctionType: TaintFunctionType.TaintFunctionType
): List[WLDiEdge[TaintNode]] = {
  val result = time(block, taintFunctionType.toString)

  taintIds = taintIds ++ result.flatMap((edge: WLDiEdge[TaintNode]) =>
    List(
      edge._1.id -> edge._1.isSource,
      edge._2.id -> edge._2.isSource
    )
  )

  result
}

def addTaintSourceIds(
    block: => List[TaintNode]
): List[TaintNode] = {
  val result = block

  taintIds =
    taintIds ++ result.map((node: TaintNode) => node.id -> node.isSource)

  result
}

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

def getTypeFromId(id: Long, nodeType: TaintNodeType) =
  cpg_typed.id(id).label.head match {
    case "CALL"                => TaintNodeType.Call
    case "METHOD"              => TaintNodeType.Method
    case "IDENTIFIER"          => TaintNodeType.Argument
    case "RETURN"              => TaintNodeType.Return
    case "METHOD_PARAMETER_IN" => TaintNodeType.Parameter
    case default               => nodeType
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

def getCodeFromId(id: Long, nodeType: TaintNodeType) =
  getTypeFromId(id, nodeType) match {
    case TaintNodeType.Argument         => getArgumentFromId(id).code.head
    case TaintNodeType.Parameter        => getParameterFromId(id).name.head
    case TaintNodeType.ParameterReverse => getParameterFromId(id).name.head
    case TaintNodeType.Return => {
      val x = getReturnFromId(id)
      if (x.size > 0) {
        ""
      } else {
        x.astChildren.code.head
      }
    }
    case TaintNodeType.Call => getCallFromId(id).code.head
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
    pSrc: TaintNode
): Map[TaintNode, TaintNodeWeight] = {
  var src = pSrc

  var weightMap: Map[TaintNode, TaintNodeWeight] = Map(
    src -> TaintNodeWeight(0)
  )

  var src_value = weightMap.getOrElse(src, TaintNodeWeight())

  while (!src_value.visited) {
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

    src = graph.nodes
      .reduceLeft(
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
      .value
    src_value = weightMap.getOrElse(src, TaintNodeWeight())
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
          isSource = false,
          "TODO"
        ))(0, EdgeType.Call),
        (TaintNode(
          getMethod(innerEdge.to.value).head.id,
          TaintNodeType.Method,
          isSource = false,
          "TODO"
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
          isSource = false,
          "TODO"
        ))(0, EdgeType.Call),
        (TaintNode(
          getMethod(innerEdge.to.value).head.id,
          TaintNodeType.Method,
          isSource = false,
          "TODO"
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
          isSource = false,
          "TODO"
        ))(0, EdgeType.Call),
        (TaintNode(
          getMethod(innerEdge.to.value).head.id,
          TaintNodeType.Method,
          isSource = false,
          "TODO"
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
          isSource = false,
          "TODO"
        ))(0, EdgeType.Call),
        (TaintNode(
          getMethod(innerEdge.to.value).head.id,
          TaintNodeType.Method,
          isSource = false,
          "TODO"
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
          isSource = false,
          "TODO"
        ) ~%+> innerEdge.to.value)(0, EdgeType.Call)
      )
    )

  methodGraph
}

case class OperationValue(
    weight: Double = 0,
    srcIndex: Int = 0,
    dstIndex: Int = 0
)

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
var sourceOperations: Map[String, Array[OperationValue]] = Map(
  "recv" -> Array(OperationValue(recv_weight, dstIndex = 2)),
  "recvfrom" -> Array(OperationValue(recv_weight, dstIndex = 2)),
  "WSARecvEx" -> Array(OperationValue(recv_weight, dstIndex = 2)),
  "HttpQueryInfo" -> Array(OperationValue(recv_weight, dstIndex = 3)),
  "HttpQueryInfoA" -> Array(OperationValue(recv_weight, dstIndex = 3)),
  "HttpQueryInfoW" -> Array(OperationValue(recv_weight, dstIndex = 3)),
  "InternetReadFile" -> Array(OperationValue(recv_weight, dstIndex = 2)),
  "InternetReadFileExA" -> Array(OperationValue(recv_weight, dstIndex = 2)),
  "InternetReadFileExW" -> Array(OperationValue(recv_weight, dstIndex = 2))
)

// Map[Function name, OperationValue]
var sinkOperations: Map[String, Array[OperationValue]] = Map(
  "strcpy" -> Array(OperationValue(cpy_weight, srcIndex = 1)),
  "wcscpy" -> Array(OperationValue(cpy_weight, srcIndex = 1)),
  "_mbscpy" -> Array(OperationValue(cpy_weight, srcIndex = 1)),
  "lstrcpyA" -> Array(OperationValue(cpy_weight, srcIndex = 1)),
  "lstrcpyW" -> Array(OperationValue(cpy_weight, srcIndex = 1)),
  "lstrcpyn" -> Array(OperationValue(cpy_weight, srcIndex = 1)),
  "lstrcpynA" -> Array(OperationValue(cpy_weight, srcIndex = 1)),
  "lstrcpynW" -> Array(OperationValue(cpy_weight, srcIndex = 1)),
  "lstrcpy" -> Array(OperationValue(cpy_weight, srcIndex = 1)),
  "lstrcat" -> Array(OperationValue(cat_weight, srcIndex = 1)),
  "lstrcatA" -> Array(OperationValue(cat_weight, srcIndex = 1)),
  "lstrcatW" -> Array(OperationValue(cat_weight, srcIndex = 1)),
  "strlen" -> Array(OperationValue(strlen_weight, srcIndex = 1)),
  "lstrlen" -> Array(OperationValue(strlen_weight, srcIndex = 1)),
  "lstrlenA" -> Array(OperationValue(strlen_weight, srcIndex = 1)),
  "lstrlenW" -> Array(OperationValue(strlen_weight, srcIndex = 1)),
  "atoi" -> Array(OperationValue(atoi_weight, srcIndex = 1)),
  "_wtoi" -> Array(OperationValue(atoi_weight, srcIndex = 1)),
  "atoi_l" -> Array(OperationValue(atoi_weight, srcIndex = 1)),
  "_wtoi_l" -> Array(OperationValue(atoi_weight, srcIndex = 1)),
  "_atodbl" -> Array(OperationValue(atoi_weight, srcIndex = 2)),
  "_atodbl_l" -> Array(OperationValue(atoi_weight, srcIndex = 2)),
  "_atoldbl" -> Array(OperationValue(atoi_weight, srcIndex = 2)),
  "_atoldbl_l" -> Array(OperationValue(atoi_weight, srcIndex = 2)),
  "_atoflt" -> Array(OperationValue(atoi_weight, srcIndex = 2)),
  "_atoflt_l" -> Array(OperationValue(atoi_weight, srcIndex = 2)),
  "atof" -> Array(OperationValue(atoi_weight, srcIndex = 1)),
  "_atof_l" -> Array(OperationValue(atoi_weight, srcIndex = 1)),
  "_wtof" -> Array(OperationValue(atoi_weight, srcIndex = 1)),
  "_wtof_l" -> Array(OperationValue(atoi_weight, srcIndex = 1)),
  "_atoi64" -> Array(OperationValue(atoi_weight, srcIndex = 1)),
  "_wtoi64" -> Array(OperationValue(atoi_weight, srcIndex = 1)),
  "_atoi64_l" -> Array(OperationValue(atoi_weight, srcIndex = 1)),
  "_wtoi64_l" -> Array(OperationValue(atoi_weight, srcIndex = 1)),
  "atol" -> Array(OperationValue(atoi_weight, srcIndex = 1)),
  "_atol_l" -> Array(OperationValue(atoi_weight, srcIndex = 1)),
  "_wtol" -> Array(OperationValue(atoi_weight, srcIndex = 1)),
  "_wtol_l" -> Array(OperationValue(atoi_weight, srcIndex = 1)),
  "atoll" -> Array(OperationValue(atoi_weight, srcIndex = 1)),
  "_wtoll" -> Array(OperationValue(atoi_weight, srcIndex = 1)),
  "_atoll_l" -> Array(OperationValue(atoi_weight, srcIndex = 1)),
  "_wtoll_l" -> Array(OperationValue(atoi_weight, srcIndex = 1)),
  "system" -> Array(OperationValue(system_weight, srcIndex = 1))
)

// Map[Function name, Src Index, OperationValue]
var indirectSourceOperations: Map[String, Array[OperationValue]] = Map(
  "<operator>.assignment" -> Array(
    OperationValue(0, srcIndex = 2, dstIndex = 1)
  ),
  "<operator>.assignmentPlus" -> Array(
    OperationValue(pointer_math_weight, srcIndex = 2, dstIndex = 1)
  ),
  "<operator>.assignmentMinus" -> Array(
    OperationValue(pointer_math_weight, srcIndex = 2, dstIndex = 1)
  ),
  "memcpy" -> Array(OperationValue(cpy_weight, srcIndex = 2, dstIndex = 1)),
  "strcpy" -> Array(OperationValue(cpy_weight, srcIndex = 2, dstIndex = 1)),
  "wcscpy" -> Array(OperationValue(cpy_weight, srcIndex = 2, dstIndex = 1)),
  "_mbscpy" -> Array(OperationValue(cpy_weight, srcIndex = 2, dstIndex = 1)),
  "lstrcpy" -> Array(OperationValue(cpy_weight, srcIndex = 2, dstIndex = 1)),
  "lstrcpyA" -> Array(OperationValue(cpy_weight, srcIndex = 2, dstIndex = 1)),
  "lstrcpyW" -> Array(OperationValue(cpy_weight, srcIndex = 2, dstIndex = 1)),
  "lstrcpyn" -> Array(OperationValue(cpy_weight, srcIndex = 2, dstIndex = 1)),
  "lstrcpynA" -> Array(OperationValue(cpy_weight, srcIndex = 2, dstIndex = 1)),
  "lstrcpynW" -> Array(OperationValue(cpy_weight, srcIndex = 2, dstIndex = 1)),
  "lstrcat" -> Array(OperationValue(cat_weight, srcIndex = 2, dstIndex = 1)),
  "lstrcatA" -> Array(OperationValue(cat_weight, srcIndex = 2, dstIndex = 1)),
  "lstrcatW" -> Array(OperationValue(cat_weight, srcIndex = 2, dstIndex = 1))
)

// Map[Function name, OperationValue]
var indirectSourceOperationsCall: Map[String, Array[OperationValue]] = Map(
  "<operator>.cast" -> Array(
    OperationValue(0, srcIndex = 1),
    OperationValue(0, srcIndex = 2)
  ),
  "<operator>.indirectIndexAccess" -> Array(
    OperationValue(pointer_math_weight, srcIndex = 1)
  ),
  "<operator>.addition" -> Array(
    OperationValue(pointer_math_weight, srcIndex = 1)
  ),
  "<operator>.addressOf" -> Array(
    OperationValue(pointer_math_weight, srcIndex = 1)
  ),
  "<operator>.indirection" -> Array(
    OperationValue(pointer_math_weight, srcIndex = 1)
  ),
  "<operator>.preIncrement" -> Array(
    OperationValue(pointer_math_weight, srcIndex = 1)
  ),
  "<operator>.postIncrement" -> Array(
    OperationValue(pointer_math_weight, srcIndex = 1)
  ),
  "<operator>.notEquals" -> Array(
    OperationValue(cmp_weight, srcIndex = 1),
    OperationValue(cmp_weight, srcIndex = 2)
  ),
  "<operator>.equals" -> Array(
    OperationValue(cmp_weight, srcIndex = 1),
    OperationValue(cmp_weight, srcIndex = 2)
  ),
  "<operator>.lessThan" -> Array(
    OperationValue(cmp_weight, srcIndex = 1),
    OperationValue(cmp_weight, srcIndex = 2)
  ),
  "<operator>.lessEqualsThan" -> Array(
    OperationValue(cmp_weight, srcIndex = 1),
    OperationValue(cmp_weight, srcIndex = 2)
  ),
  "<operator>.greaterThan" -> Array(
    OperationValue(cmp_weight, srcIndex = 1),
    OperationValue(cmp_weight, srcIndex = 2)
  ),
  "<operator>.greaterEqualsThan" -> Array(
    OperationValue(cmp_weight, srcIndex = 1),
    OperationValue(cmp_weight, srcIndex = 2)
  ),
  "<operator>.logicalNot" -> Array(OperationValue(cmp_weight, srcIndex = 1)),
  "<operator>.subtraction" -> Array(
    OperationValue(pointer_math_weight, srcIndex = 1),
    OperationValue(pointer_math_weight, srcIndex = 2)
  ),
  "<operator>.addition" -> Array(
    OperationValue(pointer_math_weight, srcIndex = 1),
    OperationValue(pointer_math_weight, srcIndex = 2)
  ),
  "<operator>.fieldAccess" -> Array(OperationValue(0, srcIndex = 1)),
  "<operator>.indirectFieldAccess" -> Array(OperationValue(0, srcIndex = 1))
)

var subSourceCall: Map[String, Array[OperationValue]] = Map(
  "<operator>.cast" -> Array(OperationValue(0)),
  "<operator>.indirectIndexAccess" -> Array(
    OperationValue(pointer_math_weight)
  ),
  "<operator>.addition" -> Array(OperationValue(pointer_math_weight)),
  "<operator>.addressOf" -> Array(OperationValue(pointer_math_weight)),
  "<operator>.indirection" -> Array(OperationValue(pointer_math_weight)),
  "<operator>.preIncrement" -> Array(OperationValue(pointer_math_weight)),
  "<operator>.postIncrement" -> Array(OperationValue(pointer_math_weight)),
  "<operator>.subtraction" -> Array(OperationValue(pointer_math_weight)),
  "<operator>.subtraction" -> Array(OperationValue(pointer_math_weight)),
  "<operator>.addition" -> Array(OperationValue(pointer_math_weight)),
  "<operator>.addition" -> Array(OperationValue(pointer_math_weight)),
  "<operator>.fieldAccess" -> Array(OperationValue(0)),
  "<operator>.indirectFieldAccess" -> Array(OperationValue(0))
)

// Map[Function name, source name Index]
val sourceCreator: Map[String, Int] = Map(
  "GetProcAddress" -> 2
)

def getSource(
    calls: Traversal[Call],
    operations: Map[String, Array[OperationValue]]
): List[WLDiEdge[TaintNode]] =
  calls
    .flatMap(call =>
      operations
        .find { case (operation: String, _) =>
          operation == call.name || s"*${operation}" == call.name
        }
        .map {
          case (operation: String, operationValues: Array[OperationValue]) =>
            operationValues.flatMap(operationValue =>
              call
                .argument(operationValue.dstIndex)
                .flatMap(arg =>
                  List(
                    (rootNode ~%+> new TaintNode(
                      call.id,
                      TaintNodeType.Source,
                      isSource = false
                    ))(0, EdgeType.Source),
                    (new TaintNode(
                      call.id,
                      TaintNodeType.Source,
                      isSource = false
                    ) ~%+>
                      new TaintNode(
                        call.argument(operationValue.dstIndex).id,
                        TaintNodeType.Argument,
                        isSource = true
                      ))(operationValue.weight, EdgeType.Call)
                  )
                )
            )
        }
    )
    .l
    .flatten

def getIndirectSource(
    nodes: Graph[TaintNode, WLDiEdge]#NodeSetT,
    operations: Map[String, Array[OperationValue]]
): List[WLDiEdge[TaintNode]] =
  nodes
    .filter((taintNode: Graph[TaintNode, WLDiEdge]#NodeT) =>
      taintNode.value.isSource
    )
    .flatMap((taintNode: Graph[TaintNode, WLDiEdge]#NodeT) =>
      getMethod(taintNode.value).call.flatMap(node =>
        operations
          .getOrElse(node.name, Array())
          .find((operationValue: OperationValue) =>
            node
              .argument(operationValue.srcIndex)
              .code
              .contains(taintNode.value.code)
          )
          .map((operationValue: OperationValue) =>
            (taintNode.value ~%+>
              new TaintNode(
                node.argument(operationValue.dstIndex).id,
                TaintNodeType.Argument,
                isSource = true
              ))(operationValue.weight, EdgeType.IndirectSource)
          )
      )
    )
    .toList

def getIndirectSourceCall(
    nodes: Graph[TaintNode, WLDiEdge]#NodeSetT,
    operations: Map[String, Array[OperationValue]]
): List[WLDiEdge[TaintNode]] =
  nodes
    .filter((taintNode: Graph[TaintNode, WLDiEdge]#NodeT) =>
      taintNode.value.isSource
    )
    .flatMap((taintNode: Graph[TaintNode, WLDiEdge]#NodeT) =>
      getMethod(taintNode.value).call.flatMap(node =>
        operations
          .getOrElse(node.name, Array())
          .find((operationValue: OperationValue) =>
            node
              .argument(operationValue.srcIndex)
              .code
              .contains(taintNode.value.code)
          )
          .map((operationValue: OperationValue) =>
            (taintNode.value ~%+> new TaintNode(
              node.id,
              TaintNodeType.Call,
              isSource = true
            ))(operationValue.weight, EdgeType.IndirectSourceCall)
          )
      )
    )
    .toList

def followSubSource(
    nodes: Graph[TaintNode, WLDiEdge]#NodeSetT,
    operations: Map[String, Array[OperationValue]]
): List[WLDiEdge[TaintNode]] =
  nodes
    .filter((taintNode: Graph[TaintNode, WLDiEdge]#NodeT) =>
      getType(taintNode.value) == TaintNodeType.Call
    )
    .flatMap((taintNode: Graph[TaintNode, WLDiEdge]#NodeT) =>
      operations
        .get(getCallFromId(taintNode.value.id).name.head)
        .map((operationValues: Array[OperationValue]) =>
          operationValues.flatMap((operationValue: OperationValue) =>
            getCallFromId(taintNode.value.id).argument
              .filterNot(arg => arg.isLiteral)
              .map(arg =>
                (taintNode.value ~%+> new TaintNode(
                  arg.id,
                  TaintNodeType.Argument,
                  isSource = true
                ))(operationValue.weight, EdgeType.IndirectSourceCall)
              )
              .l
          )
        )
    )
    .flatten
    .toList

def getCreatedSourceFunctions(
    calls: Traversal[Call],
    sourceCreator: Map[String, Int],
    sourceOperations: Map[String, Array[OperationValue]]
): Map[String, Array[OperationValue]] =
  calls
    .flatMap(node =>
      sourceOperations.flatMap {
        case (operation: String, operationValues: Array[OperationValue]) =>
          sourceCreator
            .get(node.name)
            .find(sourceNameIndex =>
              // Escaping double quote doesn't work https://github.com/scala/bug/issues/6476

              node.argument.size >= sourceNameIndex && node
                .argument(sourceNameIndex)
                .code
                .contains(s""""${operation}"""") ||
                node.code.contains(operation)
            )
            .map(_ =>
              (
                node.code,
                operationValues
              )
            )
      }
    )
    .l
    .toMap

def getCastVariables(
    calls: Traversal[Call],
    creators: Map[String, Array[OperationValue]]
) =
  calls.cast
    .flatMap((node: Call) =>
      creators
        .filter { case (operation, _) =>
          node
            .argument(2)
            .code
            .contains(operation)
        }
        .map { case (_, operationValue) =>
          (node.code, operationValue)
        }
    )
    .l
    .toMap

def getAssignmentVariables(
    calls: Traversal[Call],
    creators: Map[String, Array[OperationValue]]
): Map[String, Array[OperationValue]] =
  calls.assignment
    .flatMap((node: Call) =>
      creators
        .filter { case (operation, _) =>
          node
            .argument(2)
            .code
            .contains(operation)
        }
        .map { case (_, operationValue) =>
          (
            node.argument(1).code,
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
    .filter((taintNode: Graph[TaintNode, WLDiEdge]#NodeT) =>
      taintNode.value.isSource
    )
    .flatMap((taintNode: Graph[TaintNode, WLDiEdge]#NodeT) =>
      getMethod(taintNode.value).call
        .filter(node => node.callee.isExternal(false).nonEmpty)
        .flatMap(node =>
          node.argument
            .filter(arg =>
              arg.code == taintNode.value.code &&
                !taintIds.contains(arg.id)
            )
            .flatMap(arg =>
              if (arg.parameter.size > 0)
                List(
                  (taintNode.value ~%+> new TaintNode(
                    arg.call.id.head,
                    TaintNodeType.Call,
                    isSource = false
                  ))(0, EdgeType.Call),
                  (new TaintNode(
                    arg.call.id.head,
                    TaintNodeType.Call,
                    isSource = false
                  ) ~%+> new TaintNode(
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
    .filter((taintNode: Graph[TaintNode, WLDiEdge]#NodeT) =>
      taintNode.value.isSource
    )
    .flatMap((taintNode: Graph[TaintNode, WLDiEdge]#NodeT) =>
      getMethod(taintNode.value)
        .flatMap(method =>
          method.methodReturn.toReturn
            .filter(returnNode =>
              returnNode.code.contains(taintNode.value.code)
            )
            .map(returnNode =>
              (taintNode.value ~%+> new TaintNode(
                returnNode.id,
                TaintNodeType.Return,
                isSource = false
              ))(0, EdgeType.ReturnCall)
            )
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
          (taintNode.value ~%+> new TaintNode(
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
          param.name == taintNode.value.code &&
            !taintIds.contains(param.id)
        )
        .map(param =>
          (taintNode.value ~%+> new TaintNode(
            param.id,
            TaintNodeType.ParameterReverse,
            isSource = true
          ))(0, EdgeType.ParameterReverse)
        )
    )
    .toList

def lookForParameterCalls(
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
              new TaintNode(
                call
                  .argument(
                    getParameterFromId(taintNode.value.id).order.head
                  )
                  .id,
                TaintNodeType.Argument,
                isSource = true
              ))(0, EdgeType.ParameterSource)
          )
        else List()
      )
    )
    .toList

def lookForReturnCalls(
    nodes: Graph[TaintNode, WLDiEdge]#NodeSetT
): List[WLDiEdge[TaintNode]] =
  nodes
    .filter((taintNode: Graph[TaintNode, WLDiEdge]#NodeT) =>
      taintNode.value.nodeType == TaintNodeType.Return
    )
    .flatMap((taintNode: Graph[TaintNode, WLDiEdge]#NodeT) =>
      getMethod(taintNode.value).callIn.map(call =>
        (taintNode.value ~%+>
          new TaintNode(
            call.id,
            TaintNodeType.Call,
            isSource = true
          ))(0, EdgeType.ParameterSource)
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
        ~%+> new TaintNode(
          getObject(taintNode.value).isCall.argument(1).id.head,
          TaintNodeType.Argument,
          isSource = true
        ))(0, EdgeType.IndirectSource)
    )
    .toList

def getSinks(
    nodes: Graph[TaintNode, WLDiEdge]#NodeSetT,
    operations: Map[String, Array[OperationValue]]
): List[WLDiEdge[TaintNode]] =
  nodes
    .flatMap((taintNode: Graph[TaintNode, WLDiEdge]#NodeT) =>
      getMethod(taintNode.value).call.flatMap(node =>
        operations
          .getOrElse(node.name, Array())
          .find((operationValue: OperationValue) =>
            node
              .argument(operationValue.srcIndex)
              .code
              .contains(taintNode.value.code) &&
              taintNode.value.nodeType != TaintNodeType.Call && taintNode.value.nodeType != TaintNodeType.Return
          )
          .map((operationValue: OperationValue) =>
            (taintNode.value ~%+> new TaintNode(
              node.id,
              TaintNodeType.Sink,
              isSource = false
            ))(operationValue.weight, EdgeType.Sink)
          )
      )
    )
    .toList

def search_created_functions(
    pOperations: Map[String, Array[OperationValue]]
) = {
  var finalOperations =
    collection.mutable.Map[String, Array[OperationValue]]()
  var operations =
    collection.mutable.Map[String, Array[OperationValue]]() ++= pOperations

  while (operations.nonEmpty) {
    val (operation, value) = operations.head
    operations.remove(operation)
    finalOperations += (operation -> value)

    if (DEBUG) {
      println(s"[DEBUG]: ${operations}")
      println(s"[DEBUG]: Current Operation ${operation}")
    }
    var graph: Graph[TaintNode, WLDiEdge] = Graph()
    clear_caches()

    var currentOperationMap = Map[String, Array[OperationValue]]()
    currentOperationMap += (operation -> value)

    // debug_graph(graph)
    // graph ++= addTaintSourceIds(
    //   time(
    //     cpg_typed.identifier
    //       .filter(node => node.code == operation)
    //       .map(node => node.id)
    //       .l
    //       .map(id =>
    //         new TaintNode(
    //           id,
    //           TaintNodeType.Source,
    //           isSource = true
    //         )
    //       ),
    //     "filter code"
    //   )
    // )

    var creatorCalls = time(
      getCreatedSourceFunctions(
        cpg_typed.call,
        sourceCreator,
        currentOperationMap
      ),
      "getCreatedSourceFunctions"
    )

    debug_graph(graph)
    graph ++= addTaintSourceIds(
      time(
        creatorCalls
          .map({ case (operationInner, _) =>
            new TaintNode(
              cpg_typed.call
                .find(node => node.code == operationInner)
                .get
                .id,
              TaintNodeType.Source,
              isSource = true
            )
          })
          .toList,
        "map creatorCalls"
      )
    )

    var lastCount = 0
    while (lastCount != graph.size) {
      lastCount = graph.size
      println(s"[INFO] [COUNT] last count: ${lastCount}")

      debug_graph(graph)
      graph ++= addTaintSourceIdsFromEdge(
        getIndirectSource(
          graph.nodes,
          indirectSourceOperations
        ),
        TaintFunctionType.GetIndirectSource
      )

      debug_graph(graph)
      graph ++= addTaintSourceIdsFromEdge(
        getIndirectSourceCall(
          graph.nodes,
          indirectSourceOperationsCall
        ),
        TaintFunctionType.GetIndirectSourceCall
      )

      debug_graph(graph)
      graph ++= addTaintSourceIdsFromEdge(
        followSubSource(graph.nodes, subSourceCall),
        TaintFunctionType.FollowSubSource
      )

      debug_graph(graph)
      graph ++= addTaintSourceIdsFromEdge(
        followFunctionCalls(graph.nodes),
        TaintFunctionType.FollowFunctionCalls
      )

      debug_graph(graph)
      graph ++= addTaintSourceIdsFromEdge(
        unzipFieldAccess(graph.nodes),
        TaintFunctionType.UnzipFieldAccess
      )

      debug_graph(graph)
      graph ++= addTaintSourceIdsFromEdge(
        findReturns(graph.nodes),
        TaintFunctionType.FindReturns
      )

      debug_graph(graph)
      graph ++= addTaintSourceIdsFromEdge(
        followReturns(graph.nodes),
        TaintFunctionType.FollowReturns
      )

      debug_graph(graph)
      graph ++= addTaintSourceIdsFromEdge(
        lookForParameters(graph.nodes),
        TaintFunctionType.LookForParameters
      )

      debug_graph(graph)
      graph ++= addTaintSourceIdsFromEdge(
        lookForParameterCalls(graph.nodes),
        TaintFunctionType.LookForParameterCalls
      )

      debug_graph(graph)
      graph ++= addTaintSourceIdsFromEdge(
        lookForReturnCalls(graph.nodes),
        TaintFunctionType.LookForReturnCalls
      )

      debug_graph(graph)
    }

    operations ++= graph.nodes
      .filterNot((node: Graph[TaintNode, WLDiEdge]#NodeT) =>
        finalOperations.contains(node.value.code)
      )
      .map((node: Graph[TaintNode, WLDiEdge]#NodeT) =>
        (
          node.value.code,
          value
        )
      )
      .toMap
  }

  println(s"[INFO] [SIZE]: ${finalOperations.size}")
  if (DEBUG) {
    println(s"[DEBUG] [Operations]: ${finalOperations}")
  }

  finalOperations.toMap
}

println("[INFO] [STATUS]: Search sourceOperations")
sourceOperations =
  time(search_created_functions(sourceOperations), "sourceOperations")

taintGraph ++= getSource(cpg_typed.call, sourceOperations)
if (taintGraph.size == 1) {
  new PrintWriter(s"${output_path}/vuln.txt") {
    write("No sources found!")
    close()
  }

  throw new RuntimeException("No sources found!")
}

println("[INFO] [STATUS]: Search sinkOperations")
sinkOperations =
  time(search_created_functions(sinkOperations), "sinkOperations")

println("[INFO] [STATUS]: Search indirectSourceOperations")
indirectSourceOperations = time(
  search_created_functions(indirectSourceOperations),
  "indirectSourceOperations"
)

println("[INFO] [STATUS]: Search indirectSourceOperationsCall")
indirectSourceOperationsCall = time(
  search_created_functions(
    indirectSourceOperationsCall
  ),
  "indirectSourceOperationsCall"
)

println("[INFO] [STATUS]: Search subSourceCall")
subSourceCall = time(search_created_functions(subSourceCall), "subSourceCall")

clear_caches()

println("[INFO] [STATUS]: Tainting")
var lastCount = 0
while (lastCount != taintGraph.size) {
  lastCount = taintGraph.size
  println(s"[INFO] [COUNT]: last count: ${lastCount}")

  taintGraph ++= addTaintSourceIdsFromEdge(
    getIndirectSource(taintGraphNoRoot.nodes, indirectSourceOperations),
    TaintFunctionType.GetIndirectSource
  )
  taintGraph ++= addTaintSourceIdsFromEdge(
    getIndirectSourceCall(
      taintGraphNoRoot.nodes,
      indirectSourceOperationsCall
    ),
    TaintFunctionType.GetIndirectSourceCall
  )
  taintGraph ++= addTaintSourceIdsFromEdge(
    followSubSource(taintGraphNoRoot.nodes, subSourceCall),
    TaintFunctionType.FollowSubSource
  )
  taintGraph ++= addTaintSourceIdsFromEdge(
    followFunctionCalls(taintGraphNoRoot.nodes),
    TaintFunctionType.FollowFunctionCalls
  )
  taintGraph ++= addTaintSourceIdsFromEdge(
    unzipFieldAccess(taintGraphNoRoot.nodes),
    TaintFunctionType.UnzipFieldAccess
  )
  taintGraph ++= addTaintSourceIdsFromEdge(
    findReturns(taintGraphNoRoot.nodes),
    TaintFunctionType.FindReturns
  )
  taintGraph ++= addTaintSourceIdsFromEdge(
    followReturns(taintGraphNoRoot.nodes),
    TaintFunctionType.FollowReturns
  )
  taintGraph ++= addTaintSourceIdsFromEdge(
    lookForParameters(taintGraphNoRoot.nodes),
    TaintFunctionType.LookForParameters
  )
  taintGraph ++= addTaintSourceIdsFromEdge(
    lookForParameterCalls(taintGraphNoRoot.nodes),
    TaintFunctionType.LookForParameterCalls
  )
  taintGraph ++= addTaintSourceIdsFromEdge(
    lookForReturnCalls(taintGraphNoRoot.nodes),
    TaintFunctionType.LookForReturnCalls
  )
}

println("[INFO] [STATUS]: Sinking")
taintGraph ++= getSinks(taintGraphNoRoot.nodes, sinkOperations)

println("[INFO] [STATUS]: Weighting")
weightMap = fillShortestPaths(taintGraph, rootNode)

println("[INFO] [STATUS]: Outputting")
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
