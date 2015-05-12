(* ::Package:: *)

BeginPackage["PolyhedralComb`"]

EdmondsMatrix::usage="EdmondsMatrix[g] returns the LHS matrix of Edmonds odd set constraints Mx<=b";
EdmondsVector::usage="EdmondsVector[g] returns the RHS vector of Edmonds odd set constraints Mx<=b";

cycleVertexMatrix::usage="cycleVertexMatrix[g] returns the cycle vertex incidence matrix for both undirected and directed graphs";
cycleEdgeMatrix::usage="cycleEdgeMatrix[g] returns the cycle edge incidence matrix for undirected graphs ONLY";
cycleArcMatrix::usage="cycleArcMatrix[g] returns the cycle arc incidence matrix for directed graphs ONLY";

preferenceList::usage="preferenceList[g] returns a random prefrence list";
RothblumMatrix::usage="RothblumMatrix[g,pl] returns the Rothblum stability matrix";

tournament::usage="tournament[n] returns a random tournament";
semiCompleteD::usage="semiCompleteD[n,m] returns a random semicomplete digraph with m opposite oriented arcs ";

obsTournament::usage="obsTournament returns obstructions for Mengerian tournaments";
obsSemiCompleteD::usage="obsSemiCompleteD returns obstructions WITHIN five vertices for Mengerian semicomplete digraphs";
obstructionFreeQ::usage="obstructionFreeQ[d,obs] tests whether digraph d is free of obstructions obs";
goodTournament::usage="goodTournament[n] TRIES to return a strongly connected random tournament without obstructions within 1000 attempts";
goodSemiCompleteD::usage="goodSemiCompleteD[n,m] TRIES to return a strongly connected random semicomplete digraph without obstructions within 1000 attempts";
bfsVertexPartition::usage="bfsVertexPartition[d,r] returns a bfs vertex partition with root r. Moreover, each parition is returned in topological order if it is acyclic, otherwise a cycle list in this partition is accompanied";
maxOutDegreeVertexSet::usage="maxOutDegreeVertexSet[d] returns all vertices with maximum out degree";
bfsVertexPartitions::usage="bfsVertexPartitions[d] returns all bfs vertex partitions rooted at vertices with maximum outdegree by using bfsVertexPartition[d,r]";

feedbackVertexSetQ::usage="feedbackVertexSetQ[d,vs] tests whether vertex set vs is a feedback vertex set";

nonIsomorphicGraphs::usage="nonIsomorphicGraphs[gl] removes duplicate graphs under isomorphism";
deletionDistinctVertices::usage="deletionDistinctVertices[g] returns the deletion-distinct vertices in graph g, where two vertices are deletion-distinct if their removal result in nonisomorphic graphs";
contractionDistinctVertices::usage="contractionDistinctVertices[g] returns the contraction-distinct vertices in graph G, where two vertices are contraction-distinct if their contraction result in nonisomorphic graphs";
distinctEdges::usage="distinctEdges[g] returns distinct edges in graph G, where two edges are distinct if their removal result in nonisomorphic graphs";
minorOperation::usage="minorOperatin[g] returns nonisomorphic minors of graph g after one minor operation (vertex deletion, vertex contraction and edge deletion)";
minors::usage="minors[g] returns all minors of graph g"; 
(*Caution: minors[g] is rather slow due to its intrinsic computational hard property. 
But for specific problems, minor testing can be done in O(n2).*)


Begin["`Private`"]

(*Matrix related*)

EdmondsMatrix[g_Graph]:=Module[{el,vl,subl},
	el=EdgeList[g];
	vl=VertexList[g];
	subl=Select[Subsets[vl,{3,Infinity,2}],!EmptyGraphQ[Subgraph[g,#]]&];
	SparseArray[{i_,j_}/;(Length@Intersection[subl[[i]],List@@el[[j]]]==2):>1,{Length@subl,Length@el}]];

EdmondsVector[g_Graph]:=Module[{subl},
	subl=Select[Subsets[VertexList[g],{3,Infinity,2}],!EmptyGraphQ[Subgraph[g,#]]&];
	(Length/@subl-1)/2
];

cycleVertexMatrix[g_Graph]:=Module[{},
	Outer[Boole[MemberQ[Flatten[List@@@#1],#2]]&,FindCycle[g,Infinity,All],VertexList@g,1]];

cycleEdgeMatrix[g_Graph]:=Module[{},
	Outer[Boole[MemberQ[Sort/@#1,#2]]&,FindCycle[g,Infinity,All],EdgeList@g,1]];

cycleArcMatrix[g_Graph]:=Module[{},
	Outer[Boole[MemberQ[#1,#2]]&,FindCycle[g,Infinity,All],EdgeList@g,1]];

preferenceList[g_Graph]:=Module[{},
	Map[RandomSample[AdjacencyList[g,#]]&,VertexList@g]];

RothblumMatrix[g_Graph,pl_List]:=Module[{el},
	el=List@@@EdgeList@g;
	Outer[Boole[#1==#2\[Or]IntersectingQ[#1,#2]&&
		OrderedQ@{Position[pl[[Intersection[#1,#2][[1]]]],Complement[#2,Intersection[#1,#2]][[1]]],
				Position[pl[[Intersection[#1,#2][[1]]]],Complement[#1,Intersection[#1,#2]][[1]]]}]&,el,el,1]];

tournament[n_Integer]:=Module[{g,t},
	g=CompleteGraph[n];
	t=DirectedGraph[g,"Random",VertexLabels->"Name"]];

semiCompleteD[n_Integer,m_Integer:1]/;1<=m<=n (n-1)/2:=Module[{t,d,arcsReversed},
	t=tournament[n];
	arcsReversed=Reverse/@RandomChoice@Subsets[EdgeList[t],{m}];
	d= EdgeAdd[t,arcsReversed]];

obstructionFreeQ[d_Graph,obs_List]:=Module[{subgraphs,vcobs},
	vcobs=VertexCount/@obs;
	subgraphs=Subgraph[d,#]&/@Subsets[VertexList@d,{Min@vcobs,Min[VertexCount@d,Max@vcobs]}];
	SameQ[Or@@Flatten@Outer[IsomorphicGraphQ,subgraphs,obs],False]];

goodTournament[n_Integer]:=Module[{i,t,subgraphs},
	Do[t=tournament[n];
		If[ConnectedGraphQ[#]&&obstructionFreeQ[#,obsTournament]&@t,Return[t]],
		{i,1000}]];

goodSemiCompleteD[n_Integer,m_Integer:1]/;1<=m<=n (n-1)/2:=Module[{i,d,subgraphs},
	Do[d=semiCompleteD[n,m];
		If[ConnectedGraphQ[#]&&obstructionFreeQ[#,obsSemiCompleteD]&@d,Return[d]],
		{i,1000}]];

bfsVertexPartition[d_Graph,r_Integer]:=Module[{p,vl,vt,ct,vused},
	vt={r}; ct={}; vused=vt;
	vl=Complement[VertexList@d,vt];
	p=Reap[While[vl!={},
		vt=Complement[#,vused]&@VertexInComponent[d,vt,1];
		AppendTo[vused,#]&/@vt;
		If[AcyclicGraphQ@Subgraph[d,vt],vt=TopologicalSort@Subgraph[d,vt],ct=FindCycle[Subgraph[d,vt],{2,3},All]];
		Sow@{vt,ct};		
		vl=Complement[vl,vt]; ct={}]][[2,1]];
	Prepend[p,{{r},{}}]];

maxOutDegreeVertexSet[d_Graph]:=Module[{},
	Flatten@Position[#,Max[#]]&@VertexOutDegree@d];

bfsVertexPartitions[d_Graph]:=Module[{},
	bfsVertexPartition[d,#]&/@maxOutDegreeVertexSet@d];

feedbackVertexSetQ[d_Graph,vs_List]:=Module[{},
	d//AcyclicGraphQ[Subgraph[#,Complement[VertexList[#],vs]]]&];

(*Graph minors*)

nonIsomorphicGraphs[gl_List]:= Module[{},
	Return[DeleteDuplicates[gl,IsomorphicGraphQ[#1,#2]&]];];

distinctEdges[g_Graph]:= Module[{el},
	el=EdgeList@g;
	Return[DeleteDuplicates[el,IsomorphicGraphQ[EdgeDelete[g,#1],EdgeDelete[g,#2]]&]];];

deletionDistinctVertices[g_Graph]:= Module[{vl},
	vl=VertexList@g;
	Return[DeleteDuplicates[vl,IsomorphicGraphQ[VertexDelete[g,#1],VertexDelete[g,#2]]&]];];

contractionDistinctVertices[g_Graph]:= Module[{vl},
	vl=VertexList@g;
	Return[DeleteDuplicates[vl,IsomorphicGraphQ[VertexDelete[g,#1],VertexDelete[g,#2]]&]];];

minorOperation[g_Graph]:=Module[{vld,vlc,el,tminors},
	vld=deletionDistinctVertices@g;
	vlc=contractionDistinctVertices@g;
	el=distinctEdges@g;
	tminors=Reap[Sow@VertexDelete[g,#]&/@vld;
				Sow@VertexContract[g,#]&/@vlc;
				Sow@EdgeDelete[g,#]&/@el;][[2,1]];
	tminors=Select[tminors,UnsameQ[#,g]&]; (*Delete itself*)
	tminors=Graph/@Select[EdgeList/@tminors,UnsameQ[#,{}]&]; (*Delete isolated vertices*)
	nonIsomorphicGraphs[tminors]];

minors[g_Graph]:=Module[{tm,m},
	m=Reap[Sow[tm=minorOperation@g];
			NestWhile[Sow[tm=nonIsomorphicGraphs@Flatten@Map[minorOperation,#]]&,
						tm,UnsameQ[#,{}]&]]//Flatten;
	nonIsomorphicGraphs@m];

(*Data storage area*)

obsTournament:=Module[{f1Supp,f1,f2,obs},
	f1Supp=Graph[{1->4,4->3,3->2,2->1,2->5,4->5,5->1,5->3}];
	f1=EdgeAdd[f1Supp,#]&/@{{1->3,2->4},{1->3,4->2}};
	f2=List@Graph[{1->2,2->3,3->4,4->5,5->1,2->5,3->1,4->2,5->3,1->4}];
	obs=Union[f1,f2]
	];

obsSemiCompleteD:=Module[{f3,f41,f42Supp,f42,f43,f51,f52Supp,f52Resid,f52,f53Supp,f53Resid,f53,f54Supp,f54Resid,f54,obs},
	f3=List@Graph[{1->2,2->1,2->3,3->2,3->1,1->3}]; (*3-Ring R3*)
	f41=List@Graph[{1->2,2->3,3->2,1->3,2->4,3->4,4->1}]; (*K4 with one C2*)
	f42Supp=Graph[{1->2,2->4,4->1,2->3,3->2,3->4,4->3}]; 
	f42=nonIsomorphicGraphs[EdgeAdd[f42Supp,#]&/@{{1->3},{3->1}}]; (*K4 with two C2*)
	f43=List@Graph[{1->2,2->3,3->1,1->4,4->1,2->4,4->2,3->4,4->3}]; (*K4 with three C2, 3-wheel W3*)
	f51=List@Graph[{1->2,2->3,3->4,4->5,5->1,4->3,1->4,3->1,4->2,5->2,5->3}]; (*K5 with one C2, case 1*)
	f52Supp=Graph[{1->2,2->3,3->1,1->5,5->4,4->1,3->4,4->3}];
	f52Resid=Tuples@{{2->4,4->2},{2->5,5->2},{3->5,5->3}};
	f52=nonIsomorphicGraphs[EdgeAdd[f52Supp,#]&/@f52Resid]; (*K5 with one C2, case 2*)
	f53Supp=Graph[{1->3,3->2,2->1,1->4,4->5,5->1,3->4,4->3}];
	f53Resid=f52Resid;
	f53=nonIsomorphicGraphs[EdgeAdd[f53Supp,#]&/@f53Resid];
	f54Supp=Graph[{1->2,2->1,2->3,3->2,3->4,4->3,4->5,5->4,5->1,1->5}]; (*5-Ring*)
	f54Resid=Tuples@{{1->3,3->1},{1->4,4->1},{2->4,4->2},{2->5,5->2},{3->5,5->3}};
	f54=nonIsomorphicGraphs[EdgeAdd[f54Supp,#]&/@f54Resid]; (*K5 with one C2, case3*)
	obs=nonIsomorphicGraphs@Union[obsTournament,f3,f41,f42,f43,f51,f52,f53,f54]];

End[]

EndPackage[]
