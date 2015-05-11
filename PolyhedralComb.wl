(* ::Package:: *)

BeginPackage["PolyhedralComb`"]

EdmondsMatrix::usage="EdmondsMatrix[g] returns the LHS matrix of Edmonds odd set constraint Mx<=b";
EdmondsVector::usage="EdmondsVector[g] returns the RHS vector of Edmonds odd set constraint Mx<=b";
cycleVertexMatrix::usage="cycleVertexMatrix[g] returns the cycle vertex incidence matrix for both undirected and directed graphs";
cycleEdgeMatrix::usage="cycleEdgeMatrix[g] returns the cycle edge incidence matrix for undirected graphs only";
cycleArcMatrix::usage="cycleArcMatrix[g] returns the cycle arc incidence matrix for directed graphs only";
preferenceList::usage="preferenceList[g] returns a random prefrence table";
RothblumMatrix::usage="RothblumMatrix[g,pt] returns the Rothblum stable constraint matrix";

tournament::usage="tournament[n] generates a random tournament on n vertices";
semiCompleteD::usage="semiCompleteD[n,m] generates a random semicomplete digraph on n vertices";
obsTournament::usage="obsTournamen returns obstructions for a packing tournament";
obsSemiCompleteD::usage="obsSemiCompleteD returns all obstructions within five vertices for a packing semicomplete digraph";
packingQ::usage="packingQ[d,obs] tests whether digraph d has packing properties by checking all obstructions";
goodTournament::usage="goodTournament[n] tries to return a random tournament free of forbidden tournaments F1 and F2";
goodSemiCompleteD::usage="goodSemiCompleteD[n,m] tries to return a random semicomplete digraphs free of all forbidden structures on 5 vertices";
bfsVertexPartition::usage="bfsVertexPartition[d,r] gives a bfs partition with root r. More, it checks whether each parition is acyclic. If it is acyclic, it sorts all vertcies in topolgical order; if it is not acyclic, it returns all cycles in this pariation";
maxOutDegreeVertexSet::usage="maxOutDegreeVertexSet[d] returns all vertices with maximum out degrees";
feedbackVertexSetQ::usage"feedbackVertexSetQ[d,vs] checks whether vertex set vs is a feedback vertex set";

Begin["`Private`"]

EdmondsMatrix[g_]:=Module[{el,vl,subl},
	el=EdgeList[g];
	vl=VertexList[g];
	subl=Select[Subsets[vl,{3,Infinity,2}],!EmptyGraphQ[Subgraph[g,#]]&];
	SparseArray[{i_,j_}/;(Length@Intersection[subl[[i]],List@@el[[j]]]==2):>1,{Length@subl,Length@el}]];

EdmondsVector[g_]:=Module[{subl},
	subl=Select[Subsets[VertexList[g],{3,Infinity,2}],!EmptyGraphQ[Subgraph[g,#]]&];
	(Length/@subl-1)/2
];

cycleVertexMatrix[g_]:=Module[{},
	Outer[Boole[MemberQ[Flatten[List@@@#1],#2]]&,FindCycle[g,Infinity,All],VertexList@g,1]];

cycleEdgeMatrix[g_]:=Module[{},
	Outer[Boole[MemberQ[Sort/@#1,#2]]&,FindCycle[g,Infinity,All],EdgeList@g,1]];

cycleArcMatrix[g_]:=Module[{},
	Outer[Boole[MemberQ[#1,#2]]&,FindCycle[g,Infinity,All],EdgeList@g,1]];

preferenceList[g_]:=Module[{},
	Map[RandomSample[AdjacencyList[g,#]]&,VertexList@g]];

RothblumMatrix[g_,pl_]:=Module[{el},
	el=List@@@EdgeList@g;
	Outer[Boole[#1==#2\[Or]IntersectingQ[#1,#2]&&
		OrderedQ@{Position[pl[[Intersection[#1,#2][[1]]]],Complement[#2,Intersection[#1,#2]][[1]]],
				Position[pl[[Intersection[#1,#2][[1]]]],Complement[#1,Intersection[#1,#2]][[1]]]}]&,el,el,1]];

tournament[n_]:=Module[{g,t},
	g=CompleteGraph[n,VertexLabels->"Name"];
	t=DirectedGraph[g,"Random",VertexLabels->"Name"]];

semiCompleteD[n_,m_:1]/;1<=m<=n (n-1)/2:=Module[{g,t,arcsReversed,d},
	g=CompleteGraph[n,VertexLabels->"Name"];
	t=DirectedGraph[g,"Random",VertexLabels->"Name"];
	arcsReversed=Reverse/@RandomChoice@Subsets[EdgeList[t],{1,m}];
	d= EdgeAdd[t,arcsReversed]];

obsTournament:=Module[{obs,f1,f2},
	f1=Graph[{1->4,4->3,3->2,2->1,2->5,4->5,5->1,5->3}];
	f2=Graph[{1->2,2->3,3->4,4->5,5->1,2->5,3->1,4->2,5->3,1->4}];
	obs={EdgeAdd[f1,{1->3,2->4}],EdgeAdd[f1,{1->3,4->2}],f2}
	]

obsSemiCompleteD:=Module[{obs,f3,f41,f42,f421,f422,f43,f51,f52,f521,f522,f523,f524,f53,f531,f532,f533,f534,f54,residf54,f54all},
	f3=Graph[{1->2,2->1,2->3,3->2,3->1,1->3}]; (*3-Ring*)
	f41=Graph[{1->2,2->3,3->2,1->3,2->4,3->4,4->1}]; (*K4 with one C2*)
	f42=Graph[{1->2,2->4,4->1,2->3,3->2,3->4,4->3}]; (*K4 with two C2, two cases*)
	f421=EdgeAdd[f42,{1->3}];
	f422=EdgeAdd[f42,{3->1}];
	f43=Graph[{1->2,2->3,3->1,1->4,4->1,2->4,4->2,3->4,4->3}]; (*K4 with three C2, 3-wheel W3*)
	f51=Graph[{1->2,2->3,3->4,4->5,5->1,4->3,1->4,3->1,4->2,5->2,5->3}]; (*K5 with one C2, case 1*)
	f52=Graph[{1->2,2->3,3->1,1->5,5->4,4->1,3->4,4->3}];
	f521=EdgeAdd[f52,{2->5,2->4,3->5}];
	f522=EdgeAdd[f52,{2->5,4->2,3->5}];
	f523=EdgeAdd[f52,{5->2,2->4,3->5}];
	f524=EdgeAdd[f52,{2->5,2->4,5->3}];
	f53=Graph[{1->3,3->2,2->1,1->4,4->5,5->1,3->4,4->3}];
	f531=EdgeAdd[f52,{2->5,2->4,3->5}];
	f532=EdgeAdd[f52,{2->5,4->2,3->5}];
	f533=EdgeAdd[f52,{5->2,2->4,3->5}];
	f534=EdgeAdd[f52,{2->5,2->4,5->3}];
	f54=Graph[{1->2,2->1,2->3,3->2,3->4,4->3,4->5,5->4,5->1,1->5}]; (*5-Ring*)
	residf54={{DirectedEdge[1,3],DirectedEdge[3,1]},{DirectedEdge[1,4],DirectedEdge[4,1]},{DirectedEdge[2,4],DirectedEdge[4,2]},{DirectedEdge[2,5],DirectedEdge[5,2]},{DirectedEdge[3,5],DirectedEdge[5,3]}};
	f54all=EdgeAdd[f54,#]&/@Tuples[residf54];
	obs=obsTournament\[Union]{f3,f41,f421,f422,f43,f51,f521,f522,f523,f524,f531,f532,f533,f534}\[Union]f54all];

packingQ[d_,obs_]:=Module[{subgraphs},
		subgraphs=Subgraph[d,#]&/@Subsets[VertexList@d,{3,Min[VertexCount@d,5]}];
		SameQ[Or@@Flatten@Outer[IsomorphicGraphQ,subgraphs,obs],False]];

goodTournament[n_]:=Module[{i,t,subgraphs},
	i=1;
	While[i<=1000,
		t=tournament[n];
		subgraphs=Subgraph[t,#]&/@Subsets[VertexList@t,{5}];
		If[packingQ[t,obsTournament],Return[t]];i++]];

goodSemiCompleteD[n_,m_:1]/;1<=m<=n (n-1)/2:=Module[{i,d,subgraphs},
	i=1;
	While[i<=1000,
		d= semiCompleteD[n,m];
		subgraphs=Subgraph[d,#]&/@Subsets[VertexList@d,{3,Min[VertexCount@d,5]}];
		If[packingQ[d,obsSemiCompleteD],Return[d]];i++]];
(*
outbfsTree[d_]:=Module[{rd,bfshighlight},
	rd=ReverseGraph@d;
	bfshighlight=Reap[BreadthFirstScan[rd,RandomChoice@Flatten@Position[VertexOutDegree@d,Max[VertexOutDegree@d]],{"FrontierEdge"->Sow}]][[2,1]]//HighlightGraph[rd,#]&;
	ReverseGraph@bfshighlight];

randombfsVPartition[d_]:=Module[{p,vl,vt,ct,vused},
	p={}; ct={}; vused={};
	vt=List@RandomChoice@Flatten@Position[VertexOutDegree@d,Max@VertexOutDegree@d];
	vl=Complement[VertexList@d,vt];
	AppendTo[p,{vt,ct}];
	While[vl!={},
		AppendTo[vused,#]&/@vt;
		vt=Complement[#,vused]&@VertexInComponent[d,vt,1];
		If[AcyclicGraphQ@Subgraph[d,vt],vt=TopologicalSort@Subgraph[d,vt],ct=FindCycle[Subgraph[d,vt],{2,3},All]];
		AppendTo[p,{vt,ct}];		
		vl=Complement[vl,vt];
		ct={}];
	p];
*)

bfsVertexPartition[d_,r_]:=Module[{p,vl,vt,ct,vused},
	p={}; ct={}; vused={}; vt={r};
	vl=Complement[VertexList@d,vt];
	AppendTo[p,{vt,ct}];
	While[vl!={},
		AppendTo[vused,#]&/@vt;
		vt=Complement[#,vused]&@VertexInComponent[d,vt,1];
		If[AcyclicGraphQ@Subgraph[d,vt],vt=TopologicalSort@Subgraph[d,vt],ct=FindCycle[Subgraph[d,vt],{2,3},All]];
		AppendTo[p,{vt,ct}];		
		vl=Complement[vl,vt];
		ct={}];
	p];

maxOutDegreeVertexSet[d_]:=Module[{},
	Flatten@Position[#,Max[#]]&@VertexOutDegree@d];

feedbackVertexSetQ[d_,vs_]:=Module[{},
	d//AcyclicGraphQ[Subgraph[#,Complement[VertexList[#],vs]]]&];

End[]

EndPackage[]
