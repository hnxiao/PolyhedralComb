(* ::Package:: *)

BeginPackage["Matchings`",{"Graphs`"}]

EdmondsMatrix::usage="EdmondsMatrix[g] returns the LHS matrix of Edmonds odd set constraints Mx<=b.";
EdmondsVector::usage="EdmondsVector[g] returns the RHS vector of Edmonds odd set constraints Mx<=b.";
RothblumMatrix::usage="RothblumMatrix[g,pl] returns the Rothblum stability matrix.";
PreferenceList::usage="PreferenceList[g] returns a random prefrence list.";

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
	(Length/@subl-1)/2
];

RothblumMatrix[g_Graph,pl_List]:=Module[{el},
	el=List@@@EdgeList@g;
	Outer[Boole[#1==#2\[Or]IntersectingQ[#1,#2]&&
		OrderedQ@{Position[pl[[Intersection[#1,#2][[1]]]],Complement[#2,Intersection[#1,#2]][[1]]],
				Position[pl[[Intersection[#1,#2][[1]]]],Complement[#1,Intersection[#1,#2]][[1]]]}]&,el,el,1]];

PreferenceList[g_Graph]:=Module[{},
	Map[RandomSample[AdjacencyList[g,#]]&,VertexList@g]];


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
