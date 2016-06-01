(* ::Package:: *)

BeginPackage["Graphs`",{"IGraphM`"}]
(* Public import *)
Get["Polyhedra`"]

DeleteIsomorphicGraphs::usage="DeleteIsomorphicGraphs[gl] removes duplicate graphs under isomorphism.";

InducedSubgraphQ::usage="InducedSubgraphQ[g,subg] returns True if subg is an induced subgraph of g and False otherwise.";
ObstructionFreeQ::usage="ObstructionFreeQ[g,obstl] tests whether graph g is free of obstructions obstl.";

SubgraphsFreeQ::usage="SubgraphsFreeQ[graph,subgraphs] tests whether none of subgraphs is contained in graph.";
InducedSubgraphsFreeQ::usage="InducedSubgraphsFreeQ[graph,subgraphs] tests whether none of subgraphs is contained in graph as an induced subgraph.";

ImmersionContract::usage="ImmersionContract[d,v] returns the immersion minor of graph d after contracting vertex v.";
DeletionDistinctVertexList::usage="DeletionDistinctVertexList[g] returns the deletion-distinct vertices in graph g, where two vertices are deletion-distinct if their removal result in nonisomorphic graphs.";
ContractionDistinctVertexList::usage="ContractionDistinctVertexList[g] returns the immersion-distinct vertices in graph d.";
DeletionDistinctEdgeList::usage="DeletionDistinctEdgeList[g] returns distinct edges in graph g, the deletion of which result in nonisomorphic graphs.";
ContractionDistinctEdgeList::usage="ContractionDistinctEdgeList[g] returns distinct edges in graph g, the constraction of which result in nonisomorphic graphs.";
FirstMinorList::usage="FirstMinorList[g] returns all nonisomorphic minors of graph g after one minor operation (vertex deletion, vertex contraction and edge deletion).";
FirstImmersionList::usage="FirstImmersionList[d] returns all nonisomorphic immersions of graph d after one immersion operation (vertex deletion and immersion contraction).";
(*Caution: MinorList and ImmersionList are extremely slow due to their intrinsic computational hard property. 
But for specific problems, minor testing can be done in O(n2).*)
MinorList::usage="MinorList[g] returns all nonisomorphic minors of graph g."; 
ImmersionList::usage="ImmersionList[d] returns all nonisomorphic immersions of digraph d.";

ConnectedGraphList::usage="ConnectedGraphList[n] returns the list of connected graphs with n vertices.";

LineMultiGraphList::usage="LineMultiGraphList[n] returns the list of connected line graphs of multigraphs with n vertices.";

OrientationList::usage="OrientationList[g] returns the list of orientations of graph g.";
SuperOrientationList::usage="SuperOrientationList[g] returns the list of superorientations of graph g.";


ChromaticNumber::usage="ChromaticNumber[g] returns the chromatic number of g.";
ChromaticIndex::usage="ChromaticIndex[g] returns the chromatic index of g.";
CliqueNumber::usage="CliqueNumber[g] returns the size of  maximum clqiue of g.";
PerfectGraphQ::usage="PerfectGraphQ[g] returns True if g is perfect and False otherwise.";
BergeGraphQ::usage="BergeGraphQ[g] returns True if g is a Berge graph and False otherwise.";


FindAllClique::usage="FindAllClique[g] returns all possible cliques (not just maximal ones) in graph g.";
FindAllNonTrivialClique::usage="FindAllNonTrivialClique[g] returns all possible non-trivial cliques (of cardinality larger than two) in graph g.";
FindAllIndependentVertexSet::usage="FindAllIndependentVertexSet[g] returns all possible independent vertex set (not just maximal ones) in graph g.";


FeedbackVertexSetQ::usage="FeedbackVertexSetQ[d,vs] tests whether vertex set vs is a feedback vertex set";
FeedbackVertexSetList::usage="FeedbackVertexSetList[g] returns all minimum feedback vertex sets";


(*** HYPERGRAPHS ***)


HypergraphIncidenceMatrix::usage="HypergraphIncidenceMatrix[vl,el] returns the edge-vertex incidence matrix of the hypergraph.";
HypergraphCoveringSystem::usage="HypergraphCoveringSystem[vl,el] returns the hypergraph covering system Mx>=1, Ix>=0 as Ax<=b in list {A,b}.";

CycleVertexMatrix::usage="CycleVertexMatrix[g] returns the cycle vertex incidence matrix for both undirected and directed graphs.";
CycleEdgeMatrix::usage="CycleEdgeMatrix[g] returns the cycle edge incidence matrix for undirected graphs ONLY.";
CycleArcMatrix::usage="CycleArcMatrix[d] returns the cycle arc incidence matrix for directed graphs ONLY.";


Begin["`Private`"]


(* 
Private import
Needs["IGraphM`"]
*)


(*** DELETING ISOMORPHIC GRAPHS ***)


DeleteIsomorphicGraphs[gl_List]:= Module[{},
	DeleteDuplicatesBy[gl,CanonicalGraph]];


(*** OBSTRUCTION TEST ***)


(** INDUCED subgraph isomorphism **)

InducedSubgraphQ[g_Graph,h_Graph]:=Module[{subgl},
	subgl=Select[Subgraph[g,#]&/@Subsets[VertexList@g,{VertexCount@h}],WeaklyConnectedGraphQ];
	AnyTrue[TrueQ][IsomorphicGraphQ[#,h]&/@subgl]];

ObstructionFreeQ[g_Graph,obstl_List]:=Module[{subgl,vc},
	vc=VertexCount/@obstl;
	subgl=Select[Subgraph[g,#]&/@Subsets[VertexList@g,MinMax[vc]],WeaklyConnectedGraphQ];
	NoneTrue[TrueQ][Flatten@Outer[IsomorphicGraphQ,subgl,obstl]]];

(* Slower implementations
ObstructionFreeQ[g_Graph,obst_List]:=Module[{},
	NoneTrue[TrueQ][InducedSubgraphQ[g,#]&/@obst]];

ObstructionFreeQ[g_Graph,obstl_List]:=Module[{subgl,vc},
	vc=VertexCount/@obstl;
	subgl=Select[Subgraph[g,#]&/@Subsets[VertexList@g,MinMax[vc]],WeaklyConnectedGraphQ];
	SetAttributes[IsomorphicGraphQ,Listable];
	NoneTrue[TrueQ][Flatten@IsomorphicGraphQ[obstl,subgl]]];
*)


(** Using igraph C Library **)
(* Subgraph test *)
SubgraphsFreeQ[g_Graph,subgl_List]:=Module[{},
	NoneTrue[TrueQ][IGSubisomorphicQ[#,g]&/@subgl]];

(* Induced subgraph test *)
(*LAD algo can be used for testing INDUCED subgraph isomorphism, but it does NOT detect opposite arcs?*)
InducedSubgraphsFreeQ[g_Graph,subgl_List]:=Module[{},
	NoneTrue[TrueQ][IGLADSubisomorphicQ[#,g,"Induced"->True]&/@subgl]];


(*** MINORS AND IMMERSIONS ***)


ImmersionContract[d_Graph,v_Integer]:=Module[{vl,el,Nin,Nout,Nio},
	Nin=VertexInComponent[d,{#},1]&;
	Nout=VertexOutComponent[d,{#},1]&;
	Nio=Intersection[Nin@#,Nout@#]&;
	vl=Union[List@#,Nio@#]&@v;
	el=Flatten@Outer[DirectedEdge,Complement[Nin@#,Nio@#],Complement[Nout@#,Nio@#]]&@v;
	EdgeAdd[VertexDelete[d,vl],#]&@Complement[el,EdgeList@d]];

DeletionDistinctVertexList[g_Graph]:= Module[{vl},
	vl=VertexList@g;
	Return[DeleteDuplicates[vl,IsomorphicGraphQ[VertexDelete[g,#1],VertexDelete[g,#2]]&]];];

ContractionDistinctVertexList[d_Graph]:= Module[{vl},
	vl=VertexList@d;
	Return[DeleteDuplicates[vl,IsomorphicGraphQ[ImmersionContract[d,#1],ImmersionContract[d,#2]]&]];];

DeletionDistinctEdgeList[g_Graph]:= Module[{el},
	el=EdgeList@g;
	Return[DeleteDuplicates[el,IsomorphicGraphQ[EdgeDelete[g,#1],EdgeDelete[g,#2]]&]];];

ContractionDistinctEdgeList[g_Graph]:= Module[{el},
	el=EdgeList@g;
	Return[DeleteDuplicates[el,IsomorphicGraphQ[EdgeContract[g,#1],EdgeContract[g,#2]]&]];];

FirstMinorList[g_Graph]:=Module[{dvl,del,cel,fml},
	dvl=DeletionDistinctVertexList@g;
	del=DeletionDistinctEdgeList@g;
	cel=ContractionDistinctEdgeList@g;
	fml=Union[VertexDelete[g,#]&/@dvl,EdgeDelete[g,#]&/@del,EdgeContract[g,#]&/@cel];
	fml=Select[fml,WeaklyConnectedGraphQ];
	fml=Graph/@Select[EdgeList/@fml,UnsameQ[#,{}]&]; (*Delete isolated vertices*)
	DeleteIsomorphicGraphs[fml]];

FirstImmersionList[d_Graph]:=Module[{dvl,cvl,fiml},
	dvl=DeletionDistinctVertexList[d];
	cvl=ContractionDistinctVertexList[d];
	fiml=Union[VertexDelete[d,#]&/@dvl,ImmersionContract[d,#]&/@cvl];
	fiml=Select[fiml,WeaklyConnectedGraphQ];
	fiml=Graph/@Select[EdgeList/@fiml,UnsameQ[#,{}]&]; (*Delete isolated vertices*)
	DeleteIsomorphicGraphs@fiml];

(*Danger zone*)
MinorList[g_Graph]:=Module[{fml,ml},
	fml=FirstMinorList@g;
	ml=NestWhileList[DeleteIsomorphicGraphs@Flatten@Map[FirstMinorList,#]&,fml,UnsameQ[#,{}]&];
	DeleteIsomorphicGraphs@Flatten@ml];
(* Since recursion backtrace is extremely slow in Mma, we use Nest here instead. But a MinorList in recursive way is attached below.
MinorList[g_Graph]:=Module[{},
	Return@DeleteIsomorphicGraphs@Union[#,Flatten@Map[MinorList,#]]&@FirstMinorList[g]];
*)
ImmersionList[d_Graph]:=Module[{fiml,iml},
	fiml=FirstImmersionList@d;
	iml=NestWhileList[DeleteIsomorphicGraphs@Flatten@Map[FirstImmersionList,#]&,fiml,UnsameQ[#,{}]&];
	DeleteIsomorphicGraphs@Flatten@iml];

(*To do*)
(*
MinorQ[g,m]
*)



(* Generating functions *)

ConnectedGraphList[n_Integer]:=Import["https://github.com/hnxiao/data/blob/master/connected"<>ToString@n<>".graphml?raw=true"];
(*
ConnectedGraphList[n_Integer]:=Import["http://cs.anu.edu.au/~bdm/data/graph"<>ToString@n<>"c.g6"];
*)
(* Cannot return full list when n\[GreaterEqual]8
ConnectedGraphList[n_Integer]:=GraphData/@GraphData["Connected",n];
*)

LineMultiGraphList[n_Integer]:=Import["https://github.com/hnxiao/data/blob/master/linemulti"<>ToString@n<>"c.graphml?raw=true"];
(*
LineMultiGraphList[n_Integer]:=Module[{gl,obstl},
	gl=ConnectedGraphList[n];
	obstl=Import["~/GitHub/data/obstruction4linemulti.graphml"];
	Select[gl,ObstructionFreeQ[#,obstl]&]];
*)

(*
Caution:
We strongly suggest use utilities 'directg' or 'waterclutter2' from 'nauty'
to generate the list of orientations as well as superorientations.

The input format could be Graph6 or Sparse6.
The default output format is Digraph6, which is not supported by Mathematica.
However, it provides another output format, so call T-code(with option [-T] in directg).
T-code is a is a simple ASCII output format.
Every line contains one graph.
First the number of vertices,
then the number of arcs,
and then the list of arcs with the start first and the end then.
E.g.: 3 2 0 1 2 1 means 3 vertices, 2 arcs: 0-->1 and 2-->1.
When time permits, a interface to directg will be added.
*)

OrientationList[g_Graph]:=Module[{el,tal,al},
	el=EdgeList@g;
	tal=DirectedEdge@@@el;
	al=Tuples@Thread[List[tal,Reverse/@tal]];
	DeleteIsomorphicGraphs[Graph/@al]];

SuperOrientationList[g_Graph]:=Module[{el,tal,al},
	el=EdgeList[g];
	tal=DirectedEdge@@@el;
	al=Flatten/@Tuples[Subsets[#,{1,2}]&/@Thread[List[tal,Reverse/@tal]]];
	Graph/@al
(*Since DeleteIsomorphicGraphs dependens on DeleteDuplicates which has quadratic time complexity, I prefer not to use this function.*)
];




FindAllClique[g_Graph]:=Module[{},
	DeleteDuplicates[Join@@Map[Subsets,FindClique[g,Infinity,All]]]];

FindAllNonTrivialClique[g_Graph]:=Module[{},
	DeleteDuplicates[Join@@Map[Subsets[#,{3,Length@#}]&,FindClique[g,Infinity,All]]]];

FindAllIndependentVertexSet[g_Graph]:=Module[{},
	FindAllClique@GraphComplement[g]];


(*Feedback Vertex Sets*)
FeedbackVertexSetQ[g_Graph,vs_List]:=Module[{},
	AcyclicGraphQ[Subgraph[#,Complement[VertexList[#],vs]]]&@g];

FeedbackVertexSetList[g_Graph]:=Module[{vsl,fvsl},
	vsl=Subsets[VertexList@g,{#}]&/@Range[VertexCount@g];
	Do[fvsl=Select[vsl[[i]],FeedbackVertexSetQ[g,#]&];
		If[fvsl!={},Return@fvsl],{i,Length@vsl}]
	];


(*Devel*)
ChromaticNumber[g_Graph]:=Module[{z},
	MinValue[{z,z>0&&ChromaticPolynomial[g,z]>0},z,Integers]];
ChromaticIndex[g_Graph]:=ChromaticNumber[LineGraph[g]];

CliqueNumber[g_Graph]:=Length@@FindClique[g];

PerfectGraphQ[g_Graph]:=Module[{vl,subvl,subgl,test},
	vl=VertexList@g;
	subvl=Subsets[vl,{3,Length@vl}];
	subgl=Subgraph[g,#]&/@subvl;
	test=Equal[ChromaticNumber[#],CliqueNumber[#]]&;
	AllTrue[TrueQ][test/@subgl]];

BergeGraphQ[g_Graph]:=Module[{oddhole,oddantihole,obst},
	oddhole=CycleGraph/@Select[Range[5,Max[5,VertexCount@g]],OddQ];
	oddantihole=GraphComplement/@oddhole;
	obst=Join[oddhole,oddantihole];
	ObstructionFreeQ[g,obst]];


(*** HYPERGRAPHS ***)


HypergraphIncidenceMatrix[vl_List,el_List]:=Module[{},
	Outer[Boole[MemberQ[#1,#2]]&,el,vl,1]];

HypergraphCoveringSystem[vl_List,el_List]:=Module[{mat,vec},
	mat=Join[HypergraphIncidenceMatrix[vl,el],IdentityMatrix[Length@vl]];
	vec=Join[ConstantArray[1,Length@el],ConstantArray[0,Length@vl]];
	{-mat,-vec}];

(*Some applications*)
CycleVertexMatrix[g_Graph]:=Module[{},
	Outer[Boole[MemberQ[Flatten[List@@@#1],#2]]&,FindCycle[g,Infinity,All],VertexList@g,1]];

CycleEdgeMatrix[g_Graph]:=Module[{},
	Outer[Boole[MemberQ[Sort/@#1,#2]]&,FindCycle[g,Infinity,All],EdgeList@g,1]];

CycleArcMatrix[g_Graph]:=Module[{},
	Outer[Boole[MemberQ[#1,#2]]&,FindCycle[g,Infinity,All],EdgeList@g,1]];


End[]


EndPackage[]
