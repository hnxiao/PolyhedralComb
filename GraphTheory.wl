(* ::Package:: *)

BeginPackage["GraphTheory`"]

EdmondsMatrix::usage="EdmondsMatrix[g] returns the LHS matrix of Edmonds odd set constraints Mx<=b";
EdmondsVector::usage="EdmondsVector[g] returns the RHS vector of Edmonds odd set constraints Mx<=b";
CycleVertexMatrix::usage="CycleVertexMatrix[g] returns the cycle vertex incidence matrix for both undirected and directed graphs";
CycleEdgeMatrix::usage="CycleEdgeMatrix[g] returns the cycle edge incidence matrix for undirected graphs ONLY";
CycleArcMatrix::usage="CycleArcMatrix[d] returns the cycle arc incidence matrix for directed graphs ONLY";
PreferenceList::usage="PreferenceList[g] returns a random prefrence list";
RothblumMatrix::usage="RothblumMatrix[g,pl] returns the Rothblum stability matrix";

DeleteIsomorphicGraphs::usage="DeleteIsomorphicGraphs[gl] removes duplicate graphs under isomorphism";
DeletionDistinctVertexList::usage="DeletionDistinctVertexList[g] returns the deletion-distinct vertices in graph g, where two vertices are deletion-distinct if their removal result in nonisomorphic graphs";
DistinctEdgeList::usage="DistinctEdgeList[g] returns distinct edges in graph G, where two edges are distinct if their removal result in nonisomorphic graphs";
FirstMinorList::usage="FirstMinorList[g] returns all nonisomorphic minors of graph g after one minor operation (vertex deletion, vertex contraction and edge deletion)";
MinorList::usage="MinorList[g] returns all nonisomorphic minors of graph g"; 
(*Caution: MinorList[g] is extremely slow due to its intrinsic computational hard property. 
But for specific problems, minor testing can be done in O(n2).*)
ImmersionContract::usage="ImmersionContract[d,v] returns the immersion minor of graph d after contracting vertex v";
ImmersionDistinctVertexList::usage="ImmersionDistinctVertexList[g] returns the immersion-distinct vertices in graph d";
FirstImmersionList::usage="FirstImmersionList[d] returns all nonisomorphic immersions of graph d after one immersion operation (vertex deletion and immersion contraction)";

ObstructionFreeQ::usage="ObstructionFreeQ[d,obs] tests whether digraph d is free of obstructions obs";
ObstructionList::usage="ObstructionList[graphtype] returns the obstruction list of the given graph type";

FeedbackVertexSetQ::usage="FeedbackVertexSetQ[d,vs] tests whether vertex set vs is a feedback vertex set";

Tournament::usage="Tournament[n] returns a random tournament";
SemiCompleteDigraph::usage="SemiCompleteDigraph[n,m] returns a random semicomplete digraph with m opposite oriented arcs ";

GoodTournament::usage="GoodTournament[n] TRIES to return a strongly connected random tournament without obstructions within 1000 attempts";
GoodSemiCompleteDigraph::usage="GoodSemiCompleteDigraph[n,m] TRIES to return a strongly connected random semicomplete digraph without obstructions within 1000 attempts";
BFSVertexPartition::usage="BFSVertexPartition[d,r] returns a bfs vertex partition with root r. Moreover, each parition is returned in topological order if it is acyclic, otherwise a cycle list in this partition is accompanied";
MaxOutDegreeVertexList::usage="MaxOutDegreeVertexList[d] returns all vertices with maximum out degree";
BFSVertexPartitionList::usage="BFSVertexPartitionList[d] returns all bfs vertex partitions rooted at vertices with maximum outdegree by using BFSVertexPartition[d,r]";
HangingCycleList::usage="HangingCycleList[d,v] returns all good distinct cycles incident to vertex v in digrah v";

PossibleDigraphList::usage="PossibleDigraphList[d] returns all possible orientions in a semicomplete digraph with a given supporting structure";


Begin["`Private`"]


(*Graph matrices*)
EdmondsMatrix[g_Graph]:=Module[{el,vl,subl},
	el=EdgeList[g];
	vl=VertexList[g];
	subl=Select[Subsets[vl,{3,Infinity,2}],!EmptyGraphQ[Subgraph[g,#]]&];
	SparseArray[{i_,j_}/;(Length@Intersection[subl[[i]],List@@el[[j]]]==2):>1,{Length@subl,Length@el}]];

EdmondsVector[g_Graph]:=Module[{subl},
	subl=Select[Subsets[VertexList[g],{3,Infinity,2}],!EmptyGraphQ[Subgraph[g,#]]&];
	(Length/@subl-1)/2
];

CycleVertexMatrix[g_Graph]:=Module[{},
	Outer[Boole[MemberQ[Flatten[List@@@#1],#2]]&,FindCycle[g,Infinity,All],VertexList@g,1]];

CycleEdgeMatrix[g_Graph]:=Module[{},
	Outer[Boole[MemberQ[Sort/@#1,#2]]&,FindCycle[g,Infinity,All],EdgeList@g,1]];

CycleArcMatrix[g_Graph]:=Module[{},
	Outer[Boole[MemberQ[#1,#2]]&,FindCycle[g,Infinity,All],EdgeList@g,1]];

PreferenceList[g_Graph]:=Module[{},
	Map[RandomSample[AdjacencyList[g,#]]&,VertexList@g]];

RothblumMatrix[g_Graph,pl_List]:=Module[{el},
	el=List@@@EdgeList@g;
	Outer[Boole[#1==#2\[Or]IntersectingQ[#1,#2]&&
		OrderedQ@{Position[pl[[Intersection[#1,#2][[1]]]],Complement[#2,Intersection[#1,#2]][[1]]],
				Position[pl[[Intersection[#1,#2][[1]]]],Complement[#1,Intersection[#1,#2]][[1]]]}]&,el,el,1]];


(*Graph minors and immersions*)
DeleteIsomorphicGraphs[gl_List]:= Module[{},
	Return[DeleteDuplicates[gl,IsomorphicGraphQ[#1,#2]&]];];

DeletionDistinctVertexList[g_Graph]:= Module[{vl},
	vl=VertexList@g;
	Return[DeleteDuplicates[vl,IsomorphicGraphQ[VertexDelete[g,#1],VertexDelete[g,#2]]&]];];

DeletionDistinctEdgeList[g_Graph]:= Module[{el},
	el=EdgeList@g;
	Return[DeleteDuplicates[el,IsomorphicGraphQ[EdgeDelete[g,#1],EdgeDelete[g,#2]]&]];];

ContractionDistinctEdgeList[g_Graph]:= Module[{el},
	el=EdgeList@g;
	Return[DeleteDuplicates[el,IsomorphicGraphQ[EdgeContract[g,#1],EdgeContract[g,#2]]&]];];

FirstMinorList[g_Graph]:=Module[{dvl,del,cel,ml},
	dvl=DeletionDistinctVertexList@g;
	del=DeletionDistinctEdgeList@g;
	cel=ContractionDistinctEdgeList@g;
	ml=Reap[Sow@VertexDelete[g,#]&/@dvl;
				Sow@EdgeContract[g,#]&/@cel;
				Sow@EdgeDelete[g,#]&/@del;][[2,1]];
	ml=Graph/@Select[EdgeList/@ml,UnsameQ[#,{}]&]; (*Delete isolated vertices*)
	DeleteIsomorphicGraphs[ml]];

MinorList[g_Graph]:=Module[{tml,ml},
	ml=Reap[Sow[tml=FirstMinorList@g];
			NestWhile[Sow[tml=DeleteIsomorphicGraphs@Flatten@Map[FirstMinorList,#]]&,
						tml,UnsameQ[#,{}]&]]//Flatten;
	DeleteIsomorphicGraphs@ml];

ImmersionContract[d_Graph,v_Integer]:=Module[{vl,el,Nin,Nout,Nio},
	Nin=VertexInComponent[d,{#},1]&;
	Nout=VertexOutComponent[d,{#},1]&;
	Nio=Intersection[Nin@#,Nout@#]&;
	vl=Union[List@#,Nio@#]&@v;
	el=Flatten@Outer[DirectedEdge,Complement[Nin@#,Nio@#],Complement[Nout@#,Nio@#]]&@v;
	Fold[EdgeAdd,VertexDelete[d,vl],Complement[el,EdgeList@d]]];

ImmersionDistinctVertexList[d_Graph]:= Module[{vl},
	vl=VertexList@d;
	Return[DeleteDuplicates[vl,IsomorphicGraphQ[ImmersionContract[d,#1],ImmersionContract[d,#2]]&]];];

FirstImmersionList[d_Graph]:=Module[{dvl,ivl,iml},
	dvl=DeletionDistinctVertexList[d];
	ivl=ImmersionDistinctVertexList[d];
	iml=Reap[Sow@VertexDelete[d,#]&/@dvl;
				Sow@ImmersionContract[d,#]&/@ivl][[2,1]];
	iml=Graph/@Select[EdgeList/@iml,UnsameQ[#,{}]&]; (*Delete isolated vertices*)
	DeleteIsomorphicGraphs@iml];


(*Graph obstructions*)
ObstructionFreeQ[d_Graph,obsl_List]:=Module[{subgl,vcobs},
	vcobs=VertexCount/@obsl;
	subgl=Subgraph[d,#]&/@Subsets[VertexList@d,{Min@vcobs,Min[VertexCount@d,Max@vcobs]}];
	SameQ[Or@@Flatten@Outer[IsomorphicGraphQ,subgl,obsl],False]];

ObstructionList[s_String]:=Module[{obs,f1Supp,f1,f2,f3,f41,f42Supp,f42,f43,f51Supp,f51Resid,f51,f52Supp,f52Resid,f52,f53Supp,f53Resid,f53,f54Supp,f54Resid,f54},	
	(*begin: Data storage*)
	f1Supp=Graph[{1->4,4->3,3->2,2->1,2->5,4->5,5->1,5->3}];
	f1=EdgeAdd[f1Supp,#]&/@{{1->3,2->4},{1->3,4->2}};
	f2=List@Graph[{1->2,2->3,3->4,4->5,5->1,2->5,3->1,4->2,5->3,1->4}];
	f3=List@Graph[{1->2,2->1,2->3,3->2,3->1,1->3}]; (*3-Ring R3*)
	f41=List@Graph[{1->2,2->3,3->2,1->3,2->4,3->4,4->1}]; (*K4 with one C2*)
	f42Supp=Graph[{1->2,2->4,4->1,2->3,3->2,3->4,4->3}]; 
	f42=DeleteIsomorphicGraphs[EdgeAdd[f42Supp,#]&/@{{1->3},{3->1}}]; (*K4 with two C2*)
	f43=List@Graph[{1->2,2->3,3->1,1->4,4->1,2->4,4->2,3->4,4->3}]; (*K4 with three C2, 3-wheel W3*)
	f51Supp=Graph[{1->2,2->3,3->4,4->3,4->5,5->1,3->1,1->4,5->2}];
	f51Resid=Tuples@{{2->4,4->2},{3->5,5->3}};
	f51=DeleteIsomorphicGraphs[EdgeAdd[f51Supp,#]&/@f51Resid];
	(*f51=List@Graph[{1->2,2->3,3->4,4->5,5->1,4->3,1->4,3->1,4->2,5->2,5->3}]; (*K5 with one C2, case 1*)*)
	f52Supp=Graph[{1->2,2->3,3->1,1->5,5->4,4->1,3->4,4->3}];
	f52Resid=Tuples@{{2->4,4->2},{2->5,5->2},{3->5,5->3}};
	f52=DeleteIsomorphicGraphs[EdgeAdd[f52Supp,#]&/@f52Resid]; (*K5 with one C2, case 2*)
	f53Supp=Graph[{1->3,3->2,2->1,1->4,4->5,5->1,3->4,4->3}];
	f53Resid=f52Resid;
	f53=DeleteIsomorphicGraphs[EdgeAdd[f53Supp,#]&/@f53Resid];
	f54Supp=Graph[{1->2,2->1,2->3,3->2,3->4,4->3,4->5,5->4,5->1,1->5}]; (*5-Ring*)
	f54Resid=Tuples@{{1->3,3->1},{1->4,4->1},{2->4,4->2},{2->5,5->2},{3->5,5->3}};
	f54=DeleteIsomorphicGraphs[EdgeAdd[f54Supp,#]&/@f54Resid]; (*K5 with one C2, case3*)
	(*end: Data stroage*)
	Which[StringMatchQ[#,"Tournament",IgnoreCase->True],
		Return@Union[f1,f2],
		StringMatchQ[#,"SemiCompleteDigraph",IgnoreCase->True],
		Return@DeleteIsomorphicGraphs@Union[f1,f2,f3,f41,f42,f43,f51,f52,f53,f54]]&
		@s;
	Return[{}]];


(*Miscellaneous*)
FeedbackVertexSetQ[d_Graph,vs_List]:=Module[{},
	AcyclicGraphQ[Subgraph[#,Complement[VertexList[#],vs]]]&@d];


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
