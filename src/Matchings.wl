(* ::Package:: *)

BeginPackage["Matchings`",{"Graphs`"}]

EdmondsSystem::usage="EdmondsSystem[g] returns the Edmonds' odd set constraints Mx<=b.";
EdmondsMatrix::usage="EdmondsMatrix[g] returns the LHS matrix of Edmonds' odd set constraints Mx<=b.";
EdmondsVector::usage="EdmondsVector[g] returns the RHS vector of Edmonds' odd set constraints Mx<=b.";
RothblumMatrix::usage="RothblumMatrix[g,pl] returns the Rothblum stability matrix.";
PreferenceEdgeList::usage="PreferenceEdgeList[g] returns a random prefrence list in edges.";
PreferenceVertexList::usage="PreferenceVertexList[g] returns a random prefrence list in vertices.";

RothblumPolytope::usage="RothblumPolytope[g,p] returns the linear systme Ax<=b defining fractional stable matching polytope";
EdmondsRothblumPolytope::usage="EdmondsRothblumPolytope[g,p] returns the linear systme Ax<=b defining fractional stable matching polytope";


Begin["`Private`"]


(*** GRAPH MATRICES ***)


(* Stable matching constraints *)
EdmondsMatrix[g_Graph]:=Module[{el,vl,subl},
	el=EdgeList[g];
	vl=VertexList[g];
	subl=Select[Subsets[vl,{3,Infinity,2}],!EmptyGraphQ[Subgraph[g,#]]&];
	SparseArray[{i_,j_}/;(Length@Intersection[subl[[i]],List@@el[[j]]]==2):>1,{Length@subl,Length@el}]];

EdmondsVector[g_Graph]:=Module[{subl},
	subl=Select[Subsets[VertexList[g],{3,Infinity,2}],!EmptyGraphQ[Subgraph[g,#]]&];
	(Length/@subl-1)/2];

EdmondsSystem[g_Graph]:=Module[{el,vl,subl,mat,vec},
	el=EdgeList[g];
	vl=VertexList[g];
	subl=Select[Subsets[vl,{3,Infinity,2}],!EmptyGraphQ[Subgraph[g,#]]&];
	mat=SparseArray[{i_,j_}/;(Length@Intersection[subl[[i]],List@@el[[j]]]==2):>1,{Length@subl,Length@el}];
	vec=(Length/@subl-1)/2;
	{mat,vec}];

(*Caution: Preference List should be given in the same order with the result of EdgeList*)
RothblumMatrix[g_Graph,pl_List]:=Module[{cel,cpl,del},
(*A auto sort operation putting preference list to canonial form should be added*)
	cel=Sort/@EdgeList@g;(*Put edges in canonical form*)
	cpl=Map[Sort,pl,{2}];(*Put edges in canonical form*)
	del=dominatingEdges[cpl,#]&/@cel;
	Outer[Boole[MemberQ[#1,#2]]&,del,cel,1]];
(*Private function: Dominating edges*)
dominatingEdges[cpl_List,ce_UndirectedEdge]:=Module[{epl},
	epl=Select[cpl,MemberQ[#,ce]&];
	Apply[Union,Take[#,Position[#,ce][[1]][[1]]]&/@epl]];


(*
RothblumMatrix[g_Graph,pl_List]:=Module[{el},
	el=List@@@EdgeList@g;
	Outer[Boole[#1==#2\[Or]IntersectingQ[#1,#2]&&
		OrderedQ@{Position[pl[[Intersection[#1,#2][[1]]]],Complement[#2,Intersection[#1,#2]][[1]]],
				Position[pl[[Intersection[#1,#2][[1]]]],Complement[#1,Intersection[#1,#2]][[1]]]}]&,el,el,1]];
*)
PreferenceVertexList[g_Graph]:=Module[{},
	Map[RandomSample[AdjacencyList[g,#]]&,Sort@VertexList[g]]];

PreferenceEdgeList[g_Graph]:=Module[{},
	Map[RandomSample[IncidenceList[g,#]]&,Sort@VertexList@g]];


RothblumPolytope[g_Graph,p_List]:=Module[{A1,A2,A3,A,b},
	A1=-RothblumMatrix[g,p];
	A2=IncidenceMatrix@g;
	A3=-IdentityMatrix[EdgeCount@g];
	A=Join[A1,A2,A3];
	b=Join[ConstantArray[-1,Length@A1],ConstantArray[1,Length@A2],ConstantArray[0,EdgeCount@g]];
	List[A,b]];

EdmondsRothblumPolytope[g_Graph,p_List]:=Module[{},
	{A,b}=RothblumPolytope[g,p];
	A=Join[A,EdmondsMatrix[g]];
	b=Join[b,EdmondsVector[g]];
	List[A,b]];


End[]


EndPackage[]
