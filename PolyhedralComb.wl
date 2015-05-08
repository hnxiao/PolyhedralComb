(* ::Package:: *)

BeginPackage["PolyhedralComb`"]

EdmondsMatrix::usage"EdmondsMatrix[g] returns the LHS matrix of Edmonds odd set constraint Mx<=b";
EdmondsVector::usage"EdmondsVector[g] returns the RHS vector of Edmonds odd set constraint Mx<=b";
CycleVertexMatrix::usage="CycleVertexMatrix[g] returns the cycle vertex incidence matrix for both undirected and directed graphs";
CycleEdgeMatrix::usage="CycleEdgeMatrix[g] returns the cycle edge incidence matrix for undirected graphs only";
CycleArcMatrix::usage="CycleArcMatrix[g] returns the cycle arc incidence matrix for directed graphs only";
PreferenceTable::usage="PreferenceTable[g] returns a random prefrence table";
RothblumMatrix::usage="RothblumMatrix[g,pt] returns the Rothblum stable constraint matrix";
randomT::usage="randomT[n] generates a random tournament on n vertices";
goodRandomT::usage="goodRandomT[n] tries to return a random tournament free of forbidden tournaments F1 and F2";
randomSemiCompleteD::usage="randomSemiCompleteD[n] generates a random semicomplete digraph on n vertices";
goodSemiCompleteD::usage="goodSemiCompleteD[n] tries to return a random semicomplete digraphs free of all forbidden structures on 5 vertices";
maxOutDegreeBFSHighlight::usage=="maxOutDegreeBFSHighlight[d] highlights a bfs tree rooted at a random maximum outdegree vertex";
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

CycleVertexMatrix[g_]:=Module[{},
	Outer[Boole[MemberQ[Flatten[List@@@#1],#2]]&,FindCycle[g,Infinity,All],VertexList@g,1]];

CycleEdgeMatrix[g_]:=Module[{},
	Outer[Boole[MemberQ[Sort/@#1,#2]]&,FindCycle[g,Infinity,All],EdgeList@g,1]];

CycleArcMatrix[g_]:=Module[{},
	Outer[Boole[MemberQ[#1,#2]]&,FindCycle[g,Infinity,All],EdgeList@g,1]];

PreferenceTable[g_]:=Module[{},
	Map[RandomSample[AdjacencyList[g,#]]&,VertexList@g]];

RothblumMatrix[g_,pt_]:=Module[{el},
	el=List@@@EdgeList@g;
	Outer[Boole[#1==#2\[Or]IntersectingQ[#1,#2]&&
		OrderedQ@{Position[pt[[Intersection[#1,#2][[1]]]],Complement[#2,Intersection[#1,#2]][[1]]],
				Position[pt[[Intersection[#1,#2][[1]]]],Complement[#1,Intersection[#1,#2]][[1]]]}]&,el,el,1]];

randomT[n_]:=Module[{g,t},
	g=CompleteGraph[n,VertexLabels->"Name"];
	t=DirectedGraph[g,"Random",VertexLabels->"Name"]];

goodRandomT[n_]:=Module[{i,t,tsubgraphs,f1,f2,tforbiddens},
	i=1;
	While[i<=100,
		t=randomT[n];
		tsubgraphs=Subgraph[t,#]&/@Subsets[VertexList@t,{5}];
		f1=Graph[{1->4,4->3,3->2,2->1,2->5,4->5,5->1,5->3}];
		f2=Graph[{1->2,2->3,3->4,4->5,5->1,2->5,3->1,4->2,5->3,1->4}];
		tforbiddens={EdgeAdd[f1,{1->3,2->4}],EdgeAdd[f1,{1->3,4->2}],f2};
		If[Or@@Flatten@Outer[IsomorphicGraphQ,tsubgraphs,tforbiddens]==False,Return[t]];i++]];

randomSemiCompleteD[n_]:=Module[{g,t,arcsReversed,d},
	g=CompleteGraph[n,VertexLabels->"Name"];
	t=DirectedGraph[g,"Random",VertexLabels->"Name"];
	arcsReversed=Reverse/@RandomChoice@Subsets[EdgeList[t],{1,Floor[EdgeCount@t/3]}];
	d= EdgeAdd[t,arcsReversed]];

goodSemiCompleteD[n_]:=Module[{i,d,dsubgraphs,f1,f11,f12,f2,f3,f41,f42,f421,f422,f43,f51,f52,f521,f522,f523,f524,f53,f531,f532,f533,f534,f54,residularcsf54,f54all,dforbiddens},
	i=1;
	While[i<=100,
		d= randomSemiCompleteD[n];
		dsubgraphs=Subgraph[d,#]&/@Subsets[VertexList@d,{3,VertexCount@d}];
		f1=Graph[{1->4,4->3,3->2,2->1,2->5,4->5,5->1,5->3}];
		f11=EdgeAdd[f1,{1->3,2->4}];
		f12=EdgeAdd[f1,{1->3,4->2}];
		f2=Graph[{1->2,2->3,3->4,4->5,5->1,2->5,3->1,4->2,5->3,1->4}];
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
		residularcsf54={{DirectedEdge[1,3],DirectedEdge[3,1]},{DirectedEdge[1,4],DirectedEdge[4,1]},{DirectedEdge[2,4],DirectedEdge[4,2]},{DirectedEdge[2,5],DirectedEdge[5,2]},{DirectedEdge[3,5],DirectedEdge[5,3]}};
		f54all=EdgeAdd[f54,#]&/@Tuples[residularcsf54];
		dforbiddens={f11,f12,f2,f3,f41,f421,f422,f43,f51,f521,f522,f523,f524,f531,f532,f533,f534}\[Union]f54all;
		If[Or@@Flatten@Outer[IsomorphicGraphQ,dsubgraphs,dforbiddens]==False,Return[d]];i++]];

maxOutDegreeBFSHighlight[d_]:=Module[{rd,bfshighlight},
	rd=ReverseGraph@d;
	bfshighlight=Reap[BreadthFirstScan[rd,RandomChoice@Flatten@Position[VertexOutDegree@d,Max[VertexOutDegree@d]],{"FrontierEdge"->Sow}]][[2,1]]//HighlightGraph[rd,#]&;
	ReverseGraph@bfshighlight];
End[]

EndPackage[]
