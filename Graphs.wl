(* ::Package:: *)

BeginPackage["Graphs`",{"IGraphM`"}]
(* Public import *)

EdmondsMatrix::usage="EdmondsMatrix[g] returns the LHS matrix of Edmonds odd set constraints Mx<=b";
EdmondsVector::usage="EdmondsVector[g] returns the RHS vector of Edmonds odd set constraints Mx<=b";
RothblumMatrix::usage="RothblumMatrix[g,pl] returns the Rothblum stability matrix";
PreferenceList::usage="PreferenceList[g] returns a random prefrence list";
DominationMatrix::usage="DominationMatrix[g] returns the kernel domination matrix";
StabilityMatrix::usage="StabilityMatrix[g] returns the kernel stablity (clique-vertex incidence) matrix for graph g";

CycleVertexMatrix::usage="CycleVertexMatrix[g] returns the cycle vertex incidence matrix for both undirected and directed graphs";
CycleEdgeMatrix::usage="CycleEdgeMatrix[g] returns the cycle edge incidence matrix for undirected graphs ONLY";
CycleArcMatrix::usage="CycleArcMatrix[d] returns the cycle arc incidence matrix for directed graphs ONLY";

DeleteIsomorphicGraphs::usage="DeleteIsomorphicGraphs[gl] removes duplicate graphs under isomorphism";

InducedSubgraphs::usage="InducedSubgraphs[g,n] returns all connected induced subgraphs with n vertices";
ObstructionFreeQ::usage="ObstructionFreeQ[g,obstl] tests whether graph g is free of obstructions obstl";
ObstructionFreeQC::usage="ObstructionFreeQC[g,obstl] tests whether graph g is free of obstructions obstl";

ImmersionContract::usage="ImmersionContract[d,v] returns the immersion minor of graph d after contracting vertex v";
DeletionDistinctVertexList::usage="DeletionDistinctVertexList[g] returns the deletion-distinct vertices in graph g, where two vertices are deletion-distinct if their removal result in nonisomorphic graphs";
ContractionDistinctVertexList::usage="ContractionDistinctVertexList[g] returns the immersion-distinct vertices in graph d";
DeletionDistinctEdgeList::usage="DeletionDistinctEdgeList[g] returns distinct edges in graph g, the deletion of which result in nonisomorphic graphs";
ContractionDistinctEdgeList::usage="ContractionDistinctEdgeList[g] returns distinct edges in graph g, the constraction of which result in nonisomorphic graphs";
FirstMinorList::usage="FirstMinorList[g] returns all nonisomorphic minors of graph g after one minor operation (vertex deletion, vertex contraction and edge deletion)";
FirstImmersionList::usage="FirstImmersionList[d] returns all nonisomorphic immersions of graph d after one immersion operation (vertex deletion and immersion contraction)";
(*Caution: MinorList and ImmersionList are extremely slow due to their intrinsic computational hard property. 
But for specific problems, minor testing can be done in O(n2).*)
MinorList::usage="MinorList[g] returns all nonisomorphic minors of graph g"; 
ImmersionList::usage="ImmersionList[d] returns all nonisomorphic immersions of digraph d";

LineGraphList::usage="LineGraphList[n] returns the list of connected line graphs with n vertices";
OrientationList::usage="OrientationList[g] returns the list of orientations of graph g";
SuperOrientationList::usage="SuperOrientationList[g] returns the list of superorientations of graph g.";
KernelQ::usage="KernelQ[g,vl] yields True if vl is a kernel of graph g and False otherwise.";
KernelExistsQ::usage="KernelExistsQ[g] yields True if g has a kernel and False otherwise.";
CKIGraphQ::usage="CKIGraphQ[g] yields True if g is critical kernel imperfect (CKI) and False otherwise.";

FeedbackVertexSetQ::usage="FeedbackVertexSetQ[d,vs] tests whether vertex set vs is a feedback vertex set";
FeedbackVertexSetList::usage="FeedbackVertexSetList[g] returns all minimum feedback vertex sets";

Tournament::usage="Tournament[n] returns a random tournament";
SemiCompleteDigraph::usage="SemiCompleteDigraph[n,m] returns a random semicomplete digraph with m opposite oriented arcs ";

GoodTournament::usage="GoodTournament[n] TRIES to return a strongly connected random tournament without obstructions within 1000 attempts";
GoodSemiCompleteDigraph::usage="GoodSemiCompleteDigraph[n,m] TRIES to return a strongly connected random semicomplete digraph without obstructions within 1000 attempts";
BFSVertexPartition::usage="BFSVertexPartition[d,r] returns a bfs vertex partition with root r. Moreover, each parition is returned in topological order if it is acyclic, otherwise a cycle list in this partition is accompanied";
MaxOutDegreeVertexList::usage="MaxOutDegreeVertexList[d] returns all vertices with maximum out degree";
MinInDegreeVertexList::usage="MinInDegreeVertexList[d] returns all vertices with minimum in degree";
BFSVertexPartitionList::usage="BFSVertexPartitionList[d] returns all bfs vertex partitions rooted at vertices with maximum outdegree by using BFSVertexPartition[d,r]";
HangingCycleList::usage="HangingCycleList[d,v] returns all good distinct cycles incident to vertex v in digrah v";

PossibleDigraphList::usage="PossibleDigraphList[d] returns all possible orientions in a semicomplete digraph with a given supporting structure";


Begin["`Private`"]


(* 
Private import
Needs["IGraphM`"]
*)


(*** GRAPH MATRICES ***)


(* Stable matching constraints *)
EdmondsMatrix[g_Graph]:=Module[{el,vl,subl},
	el=EdgeList[g];
	vl=VertexList[g];
	subl=Select[Subsets[vl,{3,Infinity,2}],!EmptyGraphQ[Subgraph[g,#]]&];
	SparseArray[{i_,j_}/;(Length@Intersection[subl[[i]],List@@el[[j]]]==2):>1,{Length@subl,Length@el}]];

EdmondsVector[g_Graph]:=Module[{subl},
	subl=Select[Subsets[VertexList[g],{3,Infinity,2}],!EmptyGraphQ[Subgraph[g,#]]&];
	(Length/@subl-1)/2
];

RothblumMatrix[g_Graph,pl_List]:=Module[{el},
	el=List@@@EdgeList@g;
	Outer[Boole[#1==#2\[Or]IntersectingQ[#1,#2]&&
		OrderedQ@{Position[pl[[Intersection[#1,#2][[1]]]],Complement[#2,Intersection[#1,#2]][[1]]],
				Position[pl[[Intersection[#1,#2][[1]]]],Complement[#1,Intersection[#1,#2]][[1]]]}]&,el,el,1]];

PreferenceList[g_Graph]:=Module[{},
	Map[RandomSample[AdjacencyList[g,#]]&,VertexList@g]];

(* Kernel constraints *)
DominationMatrix[g_Graph]:=Module[{},
	Outer[Boole[MemberQ[Flatten[List@@@#1],#2]]&,VertexOutComponent[g,{#},1]&/@VertexList[g],VertexList@g,1]];

StabilityMatrix[g_Graph]:=Module[{},
	Outer[Boole[MemberQ[Flatten[List@@@#1],#2]]&,FindClique[UndirectedGraph@g,Infinity,All],VertexList@g,1]];

(* Miscellaneous *)
CycleVertexMatrix[g_Graph]:=Module[{},
	Outer[Boole[MemberQ[Flatten[List@@@#1],#2]]&,FindCycle[g,Infinity,All],VertexList@g,1]];

CycleEdgeMatrix[g_Graph]:=Module[{},
	Outer[Boole[MemberQ[Sort/@#1,#2]]&,FindCycle[g,Infinity,All],EdgeList@g,1]];

CycleArcMatrix[g_Graph]:=Module[{},
	Outer[Boole[MemberQ[#1,#2]]&,FindCycle[g,Infinity,All],EdgeList@g,1]];




(*** DELETING ISOMORPHIC GRAPHS ***)


DeleteIsomorphicGraphs[gl_List]:= Module[{},
	DeleteDuplicatesBy[gl,CanonicalGraph]];


(*** OBSTRUCTION TEST ***)


(*** Induced subgraph isomorphism ***)

InducedSubgraphs[g_Graph,n_Integer]:=Module[{},
	DeleteIsomorphicGraphs@Select[Subgraph[g,#]&/@Subsets[VertexList@g,{n}],WeaklyConnectedGraphQ]];

ObstructionFreeQDevel[g_Graph,obstl_List]:=Module[{subgl,vc},
	vc=VertexCount/@obstl;
	subgl=InducedSubgraphs[g,#]&/@vc;
	SetAttributes[IsomorphicGraphQ,Listable];
	NoneTrue[TrueQ][Flatten@IsomorphicGraphQ[obstl,subgl]]];
(* A safer way
ObstructionFreeQDevel[g_Graph,obstl_List]:=Module[{subgl,vc},
	vc=VertexCount/@obstl;
	subgl=InducedSubgraphs[g,#]&/@vc;
	NoneTrue[TrueQ][IsomorphicGraphQ/@Flatten[Thread/@Thread[{obstl, subgl}],1]]];
*)
(* Implemented in Wolfram Language *)
ObstructionFreeQ[g_Graph,obstl_List]:=Module[{subgl,vc},
	vc=VertexCount/@obstl;
	subgl=Select[Subgraph[g,#]&/@Subsets[VertexList@g,MinMax[vc]],WeaklyConnectedGraphQ];
	\[Not]Or@@Flatten@Outer[IsomorphicGraphQ,subgl,obstl]];

(* Implemented via an interface to igraph C library *)
ObstructionFreeQC[g_Graph,obstl_List]:=Module[{},
	SameQ[Flatten[IGLADFindSubisomorphisms[#,g,"Induced"->True]&/@obstl],{}]];

(* Implemented via an interface to Boost graph library (C++)
ObstructionFreeQCXX[]:Module[{},vf2_subgraph_iso];
*)

(*To do
InducedSubgraphList[g_Graph, n_Integer]
*)


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



(*** CRITICAL KERNEL IMPERFECT (CKI) GRAPHS ***)


(* Generating functions *)
ConnectedGraphList[n_Integer]:=GraphData/@GraphData["Connected",n];
(*
ConnectedGraphList[n_Integer]:=Import["http://cs.anu.edu.au/~bdm/data/graph"<>ToString@n<>"c.g6"];
*)

LineGraphList[n_Integer]:=Module[{gl,obstl},
	gl=ConnectedGraphList[n];
	obstl=Import["~/GitHub/data/obst4linemulti.graphml"];
	Select[gl,ObstructionFreeQ[#,obstl]&]];

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

(* Testing functions *)
KernelQ[g_Graph,vl_List]:=Module[{},
	Sort@VertexInComponent[g,vl,1]==Sort@VertexList[g]];

KernelExistsQ[g_Graph]:=Module[{pkl},
	pkl=FindIndependentVertexSet[g,{1,Length@VertexList[g]},All];
	Apply[Or,KernelQ[g,#]&/@pkl]];

CKIGraphQ[g_Graph]:=Module[{vl,subvl,subgl},
	vl=VertexList@g;
	subvl=Subsets[vl,{3,Length@vl-1}];
	subgl=Subgraph[g,#]&/@subvl;
	Not@KernelExistsQ[g]&&Apply[And,KernelExistsQ/@subgl]];

(* Private functions *)
NormalGraphQ::usage="NormalGraphQ[g] yields True if every clique of g has a kernel and False otherwise";
NormalGraphQ[g_Graph]:=Module[{cliquel,subgl},
	cliquel=FindClique[UndirectedGraph@g,Length@VertexList[g],All];
	subgl=Subgraph[g,#]&/@cliquel;
	Apply[And,KernelExistsQ/@subgl]];

ChordedQ::usage="ChordedQ[g,el] yields True if the directed cycle consisting of el has a (pseudo-)chord and False otherwise.";
ChordedQ[g_Graph,el_List]:=Module[{vl,vpl,pl,chordlist},
	vl=VertexList@Subgraph[g,el];
	vpl=Subsets[vl,{2}];
	pl=Union[DirectedEdge@@@vpl,Reverse/@DirectedEdge@@@vpl];
	chordlist=Complement[pl,el];
	Apply[Or,EdgeQ[g,#]&/@chordlist]];

OddChordedGraphQ::usage="OddChordedGraphQ[g] yields True if every directed cycle has a (pseudo-)chord and False otherwise.";
OddChordedGraphQ[g_Graph]:=Module[{cyclel},
	cyclel=Flatten[FindCycle[g,{#},All]&/@Select[VertexList@g,OddQ],1];
	Apply[And,ChordedQ[g,#]&/@cyclel]];


(*Feedback Vertex Sets*)
FeedbackVertexSetQ[g_Graph,vs_List]:=Module[{},
	AcyclicGraphQ[Subgraph[#,Complement[VertexList[#],vs]]]&@g];

FeedbackVertexSetList[g_Graph]:=Module[{vsl,fvsl},
	vsl=Subsets[VertexList@g,{#}]&/@Range[VertexCount@g];
	Do[fvsl=Select[vsl[[i]],FeedbackVertexSetQ[g,#]&];
		If[fvsl!={},Return@fvsl],{i,Length@vsl}]
	];


(*Min-Max properties in semicomplete digraphs*)
Tournament[n_Integer]:=Module[{g,t},
	g=CompleteGraph[n];
	t=DirectedGraph[g,"Random",VertexLabels->"Name"]];

SemiCompleteDigraph[n_Integer,m_Integer:1]/;1<=m<=n (n-1)/2:=Module[{t,d,arl},
	t=Tournament[n];
	arl=Reverse/@RandomChoice@Subsets[EdgeList[t],{m}];
	d= EdgeAdd[t,arl]];

GoodTournament[n_Integer]:=Module[{i,t,subgl},
	Do[t=Tournament[n];
		If[ConnectedGraphQ[#]&&ObstructionFreeQ[#,ObstructionList["Tournament"]]&@t,Return[t]],
		{i,1000}]];

GoodSemiCompleteDigraph[n_Integer,m_Integer:1]/;1<=m<=n (n-1)/2:=Module[{i,d,subgl},
	Do[d=SemiCompleteDigraph[n,m];
		If[ConnectedGraphQ[#]&&ObstructionFreeQ[#,ObstructionList["SemiCompleteDigraph"]]&@d,Return[d]],
		{i,1000}]];

BFSVertexPartition[d_Graph,r_Integer]:=Module[{p,vl,vt,ct,vused},
	vt={r}; ct={}; vused=vt; vl=Complement[VertexList@d,vt];
	p=Reap[While[vl!={},
		vt=Complement[#,vused]&@VertexInComponent[d,vt,1];
		AppendTo[vused,#]&/@vt;
		If[AcyclicGraphQ@Subgraph[d,vt],vt=TopologicalSort@Subgraph[d,vt],ct=FindCycle[Subgraph[d,vt],{2,3},All]];
		Sow@{vt,ct};		
		vl=Complement[vl,vt]; ct={}]][[2,1]];
	Prepend[p,{{r},{}}]];

MaxOutDegreeVertexList[d_Graph]:=Module[{},
	Flatten@Position[#,Max[#]]&@VertexOutDegree@d];

MinInDegreeVertexList[d_Graph]:=Module[{},
	Flatten@Position[#,Min[#]]&@VertexInDegree@d];

BFSVertexPartitionList[d_Graph]:=Module[{},
	BFSVertexPartition[d,#]&/@MaxOutDegreeVertexList@d];

HangingCycleList[d_Graph,v_Integer]:=Module[{vl,c2l,c3l,subg,cbad,td,ind},
	ind={};
	c2l=FindCycle[{d,v},{2},All];
	vl=Intersection[VertexInComponent[d,{v},1],VertexOutComponent[d,{v},1]];
	td=VertexDelete[d,Select[vl,UnsameQ[#,v]&]];
	c3l=FindCycle[{td,v},{3},All];
	subg=Subgraph[td,#]&@Union@Flatten[c3l/.DirectedEdge->List];
	cbad=FindCycle[subg,{2},All];
	If[cbad!={},Do[If[Flatten[Intersection[c3l[[i]],#]&/@cbad]!={},AppendTo[ind,i]],{i,Length@c3l}]];
	Union[c2l,Delete[c3l,List/@ind]]];

PossibleDigraphList[dsupp_Graph]:=Module[{el},
	el=DirectedEdge@@@{#,Reverse@#}&/@EdgeList@GraphComplement@UndirectedGraph@dsupp;
	EdgeAdd[dsupp,#]&/@Tuples[el]];


End[]


EndPackage[]
