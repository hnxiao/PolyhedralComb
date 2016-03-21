(* ::Package:: *)

(*
This package contains an implementation
of Avis-Fukuda algorithm for enumerating all 
vertices of a convex polyhedra given by a system
of linear inequalities.

For a given m by n matrix A and m-dimensional vector b,
VertexEnumeration[A,b] finds all vertices of the polyhedron P={x:Ax\[LessEqual]b,x\[GreaterEqual]0}

In particular, these implementions can deal, in principle,
with any rational or floating-point real input with unlimited sizes m and n.

As a drawback, the actual time and space complexity is higher than it was originally stated in [1].
This is partly due to the way Mathematica  is implemented, and also due to our intention to make the program simple.
However it might be still useful for small polytopes, say, of dimension less than or equal to 8.

Another thing is that this package does not detect unboundness

[1] D. Avis and K. Fukuda, 'A pivoting algorithm for convex hulls and vertex enumeration of arrangements and polyhedra,'
Discrete and Computational Geometry, 1992, Volume 8, Issue 3, pp 295-313.
*)


BeginPackage["VertexEnumeration`"]

Unprotect[VE]
Unprotect[VertexEnumeration]

VE::usage="VE[A,b] is a short form of VertexEnumeration[A,b].";
VertexEnumeration::usage="VertexEnumeration[A,b] returns the list of all vertices of the polyhedron P={x:Ax<=b,x>=0}.";

Options[VertexEnumeration]={SearchTree -> False, ZeroVariables -> True, MonitoringFile -> "/dev/null"}


Begin["`Private`"]


VE[mat_?MatrixQ,vec_?VectorQ, opts___Rule]:=VertexEnumeration[mat,vec,opts]

VertexEnumeration[mat_?MatrixQ,vec_?VectorQ,opts___Rule]:=
	Block[{dic,i,j,m,n,bv,nbv,flattenbout,bout,obe,output,dlist,opt1,opt2},
		opt1 = SearchTree /. {opts} /. Options[VertexEnumeration];
		opt2 = ZeroVariables /. {opts} /. Options[VertexEnumeration];
		{m,n} = Dimensions[mat];
		dic = Transpose[Append[Transpose[-mat],vec]];
		AppendTo[dic,Append[Table[0,{n}],0]];
	(* get dic, bv, nbv for Bland. Warnig nbv has been chanded.*)
		{dic,bv,nbv} = CrissCross[dic,Range[n+1,m+n],Range[n],m+1,n+1,opts];
	(* feasiblity check *)
		If[InfeasibleQ[dic], Message[VertexEnumeration::Infeasible];Return[{}]];
	(* shape up dic for Bland *)
		dic = Drop[dic,-1];
		If[DegenerateQ[Last[Transpose[dic]]],
		(* There is degeneracy *)
			(* obe looks like {{{dic,bv,nbv},{dic,bv,nbv}}, dlist0} *)
			obe= OptimalBasesEnumeration[Table[-dic[[i,j]],{i,m},{j,n}],Table[dic[[i,n+1]],{i,m}],bv,nbv];
			(* bout looks like
			 {{{{Value of bv,bv,nbv},{Value of bv,bv,nbv},...},dlist},{{{Value of bv,bv,nbv},...},dlist},...} *)
			bout = Map[ Function[BSearch[#[[1]],#[[2]],#[[3]],opts]],obe[[1]]];
			(* flattenbout looks like {{Value of bv,bv,nbv},{Value of bv,bv,nbv},....} but no dupilicat startpoint*)
			flattenbout = Flatten[Map[Function[#[[1]]],bout],1];
			output = {Map[Function[Dic2Vertex[ #[[1]],#[[2]],#[[3]],Range[n]]],flattenbout]};
			If[opt2, AppendTo[output, Map[ Function[ZeroVar[#[[1]],#[[2]],#[[3]],opts]], flattenbout]]];
			If[opt1, 
				dlist = Bout2Dlist[bout,obe[[2]]];
				AppendTo[output,dlist[[1]]];
				AppendTo[output,dlist[[2]]]],
		(* There is not degeneracy *)
			(* dic and mat must be same shape *)
			AppendTo[dic,Append[Table[-1,{n}],0]];
			bout = BSearch[dic,bv,nbv,opts];
			output = {Map[ Function[Dic2Vertex[ #[[1]],#[[2]],#[[3]],Range[n]]],bout[[1]]]};
			If[opt2, AppendTo[output, Map[ Function[ZeroVar[#[[1]],#[[2]],#[[3]],opts]],
			                            bout[[1]]]]];
			If[opt1, AppendTo[output, Father2Edge[Dlist2Father[bout[[2]]]]]]
		];
		output[[1]]
	]

Options[CrissCross] = { NegativeTest-> Function[Negative[Chop[N[Simplify[#]]]]]}
Options[ZeroVar] = { NegativeTest-> Function[Negative[Chop[N[Simplify[#]]]]]}
Options[BSearch] = {SearchTree -> False, NegativeTest-> Function[Negative[Chop[N[Simplify[#]]]]], MonitoringFile->"/dev/null"}

VertexEnumeration::Infeasible = "linear inequality system is infeasible."


Bout2Dlist[bout_List,dlist0_List]:=
	Block[{i,j,dlist,boutlength,dlist0rule},
		dlist =  Map[ Function[Father2Edge[Dlist2Father[#[[2]]]]], bout];
		boutlength = Map[Function[Length[#[[1]]]],bout];
		boutlength = Prepend[Table[Sum[boutlength[[i]],{i,1,j}],{j,Length[boutlength]-1}],0];
		dlist += boutlength;
		dlist0rule = Table[ Rule[i, boutlength[[i]] + 1], {i,Length[boutlength]}];
		AppendTo[dlist,dlist0 /. dlist0rule];
		{Flatten[dlist,1],boutlength+1}
	]

Zerovar::usage="Zerovar[Value of bv, Name of bv,Name of nbv] shows the variable names with value 0.";
ZeroVar[ValueOfBv_?VectorQ,bv_?VectorQ,nbv_?VectorQ,opts___Rule]:=
	Block[{m,out={}},
		m=Length[ValueOfBv];
		SimpleNegative := NegativeTest /. {opts} /. Options[ZeroVar];
		out=Map[Function[SimpleSameQ[#,0]],ValueOfBv];
		Join[nbv,Map[Function[bv[[#[[1]]]]],Position[out,True]]]
	]

Father2Edge[fathers_?VectorQ]:= Map[{#,fathers[[#]]}&,Range[2,Length[fathers]]]

Dlist2Father[dlist_?VectorQ]:=
	Block[{po,dist,father,fathers={1}},
	(* first element in dist must be 0 and Length[dlist] => 2*)
		For[po = 2, po <= Length[dlist], ++po,
			dist =  dlist[[po]];
			father = po - 1;
			--dist;
		(* At first step a element in dist must be 1 *)
			While[dist > 0,
				father = fathers[[father]];
				--dist
			];
			AppendTo[fathers,father];
		];
		fathers
	]

Dic2Vertex::usage="Dic2Vertex[value of bv, name of bv, name of nbv, ver] returns the vertex associated with ver.";
Dic2Vertex[valueofbv_?VectorQ,bv_?VectorQ,nbv_?VectorQ,ver_?VectorQ]:=
	Map[Function[If[ MemberQ[nbv,#],
	                   0,valueofbv[[Position[bv,#][[1,1]]]]]],
	    ver]

BSearch::usage="BSearch[mat,b,n] returns the set of all basic feasible solutions for the input mat, b, n, {value of bv, name of bv, name of nbv}.";
BSearch[dict_?MatrixQ,opts___Rule]:=
	Block[{m,n,bv,nbv},
		{m,n}=Dimensions[dict];
		bv = Range[m-1];
		nbv = Range[m, m+n-2];
		BSearch[dict,bv,nbv,opts]
	]
BSearch[origdict_?MatrixQ,origbv_?VectorQ,orignbv_?VectorQ,opts___Rule]:=
	Block[{ bv=origbv,nbv=orignbv,dict=origdict,m,n,i=1,j=1,opt1,MonitoringFile,
	        result,dist=1,distlist = {0},bvposi,nbvposi},
		opt1 = SearchTree /. {opts} /. Options[BSearch];
		MonitoringFile = MonitoringFile /. {opts} /. Options[BSearch];
		SimpleNegative := NegativeTest /. {opts} /. Options[BSearch];
		{m,n}=Dimensions[dict];
		bvposi = Flatten[Map[Position[bv,#] & ,Sort[bv]]];
		nbvposi = Flatten[Map[Position[nbv,#] & ,Sort[nbv]]];
		If[opt1,
			result ={{Drop[Transpose[origdict][[n]],-1],origbv,orignbv}};
			Write[MonitoringFile,Last[result][[3]]],
			If[LexMin[origdict,origbv,orignbv,m,n], 
				result ={{Drop[Transpose[origdict][[n]],-1],origbv,orignbv}};
				Write[MonitoringFile,Last[result][[3]]],
				result = {}]];
		While[ ((i < m) || (origbv != bv)),
			While[ (i <  m && Not[BlandSelectQ[dict,bv,nbv,i,j,m,n,bvposi]]),
				++j;
				If[ j >= n, j = 1; ++i]
			];
			If[ i < m,
				{dict,bv,nbv} = VEPivot[dict,bv,nbv,i,j,m,n];
				bvposi = Flatten[Map[Position[bv,#] & ,Sort[bv]]];
				nbvposi = Flatten[Map[Position[nbv,#] & ,Sort[nbv]]];
				
(*
				Print["."];
*)
				If[opt1,
					AppendTo[result,{Drop[Transpose[dict][[n]],-1],bv,nbv}];
					Write[MonitoringFile,Last[result][[3]]];
					AppendTo[distlist,dist];
					dist = 1,
					If[LexMin[dict,bv,nbv,m,n],
						AppendTo[result,{Drop[Transpose[dict][[n]],-1],bv,nbv}];
						Write[MonitoringFile,Last[result][[3]]];
						AppendTo[distlist,dist];
						dist = 1;
					];
				];
				{i,j}={1,1},
				{i,j}=BlandSelect[dict,bv,nbv,bvposi,nbvposi];
				If[ (i < m && j < n),
					{dict,bv,nbv}=VEPivot[dict,bv,nbv,i,j,m,n];
					bvposi = Flatten[Map[Position[bv,#] & ,Sort[bv]]];
					nbvposi = Flatten[Map[Position[nbv,#] & ,Sort[nbv]]];
					++j;
					++dist;
					If[ j >= n, j = 1; ++i]
				];
			];
		];
	{result,distlist}
	]

BlandSelect::usage="BlandSelect[mat,bv,nbv] gives a pivot position selected by Bland's rule.";
BlandSelect[dict_?MatrixQ,bv_?VectorQ,nbv_?VectorQ]:=
	Block[{bvposi,nbvposi},
		bvposi = Flatten[Map[Position[bv,#] & , Sort[bv]]];
		nbvposi = Flatten[Map[Position[nbv,#] & , Sort[nbv]]];
		BlandSelect[dict,bv,nbv,bvposi,nbvposi]
	]
BlandSelect[dict_?MatrixQ,bv_?VectorQ,nbv_?VectorQ,bvposi_?VectorQ,nbvposi_?VectorQ]:=
	Block[{i,j},
		j = FirstElement[SimplePositive,Last[dict],nbvposi];
		i = NegSmallest[
		                Transpose[dict][[j]],bvposi,
		                Last[Transpose[dict]]
		               ][[1]];
		{i,j}
	]

BlandSelectQ::usage="BlandSelectQ[mat,bv,nbv,i,j] returns True if and only if {i,j}==
BlandSelect[mat,bv,nbv].";
BlandSelectQ[origdict_?MatrixQ,origbv_?VectorQ,orignbv_?VectorQ,i_Integer,j_Integer,m_Integer,n_Integer]:=
	BlandSelectQ[origdict,origbv,orignbv,i,j,m,n,Flatten[Map[Position[origbv,#] & ,Sort[origbv]]]]	
BlandSelectQ[origdict_?MatrixQ,origbv_?VectorQ,orignbv_?VectorQ,i_Integer,j_Integer,m_Integer,n_Integer,bvposi_?VectorQ]:=
	Block[{dict,bv,nbv},
		BlandFilter[origdict,origbv,orignbv,i,j,m,n,bvposi] &&
		(
		 {dict,bv,nbv}=VEPivot[origdict,origbv,orignbv,i,j,m,n];
		 SameQ[{i,j},BlandSelect[dict,bv,nbv]]
		)
	]

CrissCross::usage="CrissCross[mat,bv,nbv,m,n] solves the linear program given by a dictionary {mat,bv,nbv} and outputs a terminal dictionary.";
CrissCross[dict_?MatrixQ,opts___Rule]:=
	Block[{m,n,bv,nbv},
		{m,n}=Dimensions[dict];
		bv = Range[n,m+n-2];
		nbv = Range[n-1];
		CrissCross[dict,bv,nbv,m,n,opts]
	]
CrissCross[origdict_?MatrixQ,origbv_?VectorQ,orignbv_?VectorQ,opts___Rule]:=
	Block[{m,n},
		{m,n}=Dimensions[origdict];
		CrissCross[origdict,origbv,orignbv,m,n,opts]
	]
CrissCross[origdict_?MatrixQ,origbv_?VectorQ,orignbv_?VectorQ,m_Integer,n_Integer,opts___Rule]:=
	Block[{bv=origbv,nbv=orignbv,dict=origdict,i,j},
		SimpleNegative := NegativeTest /. {opts} /. Options[CrissCross];
		For[{i,j}=CrissCrossSelect[dict,bv,nbv,m,n],(i < m && j < n),
			{i,j}=CrissCrossSelect[dict,bv,nbv,m,n],
			{dict,bv,nbv}=VEPivot[dict,bv,nbv,i,j,m,n]
		];
		{dict,bv,nbv}
	]

OptimalBasesEnumeration::usage="OptimalBasesEnumeration[mat,b] gives the set of variable
pairs obtaining an optimal basis.";
OptimalBasesEnumeration[mat_?MatrixQ,vec_?VectorQ,bv_?VectorQ,nbv_?VectorQ]:=
	Block[{dic,degenerateBasicVariables,i,m,n,tmp,output},
		{m,n} = Dimensions[mat];
		degenerateBasicVariables = Flatten[Position[vec,0]];
		dic = mat[[degenerateBasicVariables]];
		AppendTo[dic,Table[1,{n}]];
		dic = Append[Transpose[dic],Append[Table[-1,{Length[degenerateBasicVariables]}],0]];
(*
		bv = Table[i,{i,n+1,m+n}];
		nbv = Table[i,{i,n}];
*)
(* this is dual, so bv and nbv are exchanged *)
		tmp = BSearch[dic,nbv,bv[[degenerateBasicVariables]],SearchTree->True,MonitoringFile->"/dev/null"];
		dic = Transpose[Append[Transpose[-mat],vec]];
		AppendTo[dic,Append[Table[-1,{n}],0]];
		output = Map[ Function[MakeSequence[dic,bv,nbv,GetChangeBaseVariableNames[bv,nbv,#[[3]],#[[2]]]]], tmp[[1]]];
		output = {Map[Function[ExecVEPivotSequence[dic,bv,nbv,#]], output]};
		AppendTo[output,  Father2Edge[Dlist2Father[tmp[[2]]]]];
		output
	]

DegenerateQ::usage="DegenerateQ[vec] gives True if vec contains 0. It is used to recognize degenerate dictionary.";
DegenerateQ[vec_?VectorQ]:=Count[vec,0]!=0

InfeasibleQ::usage="InfeasbleQ[mat] gives True if mat is infeasible.";
InfeasibleQ[mat_?MatrixQ]:=
	Apply[Or,Map[InfeasibleRowQ,Drop[mat,-1]]]


ForAllQ[func_,list1_List]:= Apply[And, Map[func, list1]]

LexMin::usage="LexMin[mat,bv,nbv,m,n] returns True if the dictionary {mat,bv,nbv} is lexicographically minimum for representing the current solution.";
LexMin[dic_?MatrixQ,bv_?VectorQ,nbv_?VectorQ]:=
	Block[{m,n},
		{m,n}=Dimensions[dic];
		LexMin[dic,bv,nbv,m,n]
	]
LexMin[dic_?MatrixQ,bv_?VectorQ,nbv_?VectorQ,m_Integer,n_Integer]:=
	Block[{i,j},
		For[i = 1, i < m , ++i,
			If[SimpleSameQ[0,dic[[i,n]]],
				For[j = 1, j < n, ++j,
					If[ Not[SimpleSameQ[0,dic[[i,j]]]] && bv[[i]]  > nbv[[j]], 
					    Return[False]]
					]
				]
			];
		True
	]

BlandFilter::usage="BlandFilter[mat,bv,nbv,i,j,m,n] is filter (necesarily True) for {i,j}==
BlandSelect[mat,bv,nbv].";
BlandFilter[dict_?MatrixQ,bv_?VectorQ,nbv_?VectorQ,i_Integer,j_Integer]:=
	Block[{m,n},
		{m,n}=Dimensions[dict];
		BlandFilter[dict,bv,nbv,i,j,m,n,Flatten[Map[Position[bv,#] & ,Sort[bv]]]]
	]
BlandFilter[dict_?MatrixQ,bv_?VectorQ,nbv_?VectorQ,i_Integer,j_Integer,m_Integer,n_Integer]:=
		BlandFilter[dict,bv,nbv,i,j,m,n,Flatten[Map[Position[bv,#] & ,Sort[bv]]]]
BlandFilter[dict_?MatrixQ,bv_?VectorQ,nbv_?VectorQ,i_Integer,j_Integer,m_Integer,n_Integer,bvposi_?VectorQ]:=
	( SimpleNegative[dict[[i,j]]] && SimpleNegative[dict[[m,j]]] &&
	  SimpleSameQ[-dict[[i,n]]/dict[[i,j]],
	              NegSmallest[Transpose[dict][[j]],bvposi,Last[Transpose[dict]]][[2]]]
	)

CrissCrossSelect::usage="CrissCrossSelect[mat,bv,nbv,m,n] gives the pivot position
selected by the Criss-Cross rule.";
CrissCrossSelect[dict_?MatrixQ,bv_?VectorQ,nbv_?VectorQ]:=
	Block[{m,n},
		{m,n}=Dimensions[dict];
		CrissCrossSelect[dict,bv,nbv,m,n]
	]
CrissCrossSelect[dict_?MatrixQ,bv_?VectorQ,nbv_?VectorQ,m_Integer,n_Integer]:=
	Block[{i,j,bvposi,nbvposi},
		bvposi = Flatten[Map[ Position[bv,#] & ,Sort[bv]]];
		nbvposi = Flatten[Map[ Position[nbv,#] & ,Sort[nbv]]];
		i = FirstElement[SimpleNegative,Last[Transpose[dict]],bvposi];
		j = FirstElement[SimplePositive,Last[dict],nbvposi];
		Which[
			i == m, i = FirstElement[SimpleNegative,Transpose[dict][[j]],bvposi],
			j == n, j = FirstElement[SimplePositive,dict[[i]],nbvposi],
			nbv[[j]] > bv[[i]], j = FirstElement[SimplePositive,dict[[i]],nbvposi],
			True,   i = FirstElement[SimpleNegative,Transpose[dict][[j]],bvposi];
		];
		{i,j}
	]

FirstElement::usage="FirstElement[function,list1[,list2]] gives a position on list1 (ordered by list2),that is True at first time.";	 
FirstElement[func_,list1_List,list2_List]:=
	Block[{i},
		For[i = 1,i <= Length[list2],++i,
			If[func[list1[[list2[[i]]]]],Return[list2[[i]]]]];
			i
	]
FirstElement[func_,list1_List]:=
	Block[{i},
		For[i = 1, i <= Length[list1], ++i,
		If[func[list1[[i]]],Return[i]]];
		i
	]

NegSmallest::usage="Ratio Function used by the Simplex Method";
NegSmallest[list1_List,list2_List,list3_List]:=
	Block[{i,posi,tmpval,val=Infinity},
		For[i = 1,i <= Length[list2],++i,
			If[
				(
				 SimpleNegative[list1[[list2[[i]]]]] &&
				 SimpleGreater[val,
				               tmpval = -(list3[[list2[[i]]]]/list1[[list2[[i]]]])]
				),
				posi = i;
				val = tmpval
			];
		];
		(* val = Infinity -> nothing happens. Never happens *)
		If[SameQ[Infinity,val], {i,val}, {list2[[posi]],val}]
	]

VEPivot::usage="VEPivot[mat,r,s,b,n] performs a pivot operation on mat with row:r and 
column:s and updates basis b and nonbasis n. Last 2 arguments are optional.";
VEPivot[d_?MatrixQ,bv_?VectorQ,nbv_?VectorQ,i_Integer,j_Integer,m_Integer,n_Integer]:=
	Block[{tmpbv,tmpnbv},
		{tmpbv,tmpnbv} = {bv,nbv};
		{tmpbv[[i]],tmpnbv[[j]]}={tmpnbv[[j]],tmpbv[[i]]};
		{VEPivot[d,i,j,m,n],tmpbv,tmpnbv}
	]
VEPivot[d_?MatrixQ,bv_?VectorQ,nbv_?VectorQ,i_Integer,j_Integer]:=
	Block[{tmpbv,tmpnbv},
		{tmpbv,tmpnbv} = {bv,nbv};
		{tmpbv[[i]],tmpnbv[[j]]}={tmpnbv[[j]],tmpbv[[i]]};
		{VEPivot[d,i,j],tmpbv,tmpnbv}
	]
VEPivot[d_?MatrixQ,r_Integer,s_Integer]:=
	Block[{m,n},
		{m,n}=Dimensions[d];
		VEPivot[d,r,s,m,n]
	]
VEPivot[d_?MatrixQ,r_Integer,s_Integer,m_Integer,n_Integer]:=
  Block[{i,j},
	Simplify[
	  Table[
	    Which[ (i == r) && (j == s), 1 / d[[i,j]],
		   (i == r) && (j != s), -(d[[i,j]]/d[[r,s]]),
		   (i != r) && (j == s), d[[i,j]]/d[[r,s]],
		   True, d[[i,j]] - ((d[[r,j]] * d[[i,s]]) / d[[r,s]])
		 ],{i,m},{j,n}
	       ]
	     ]
	   ]

GetChangeBaseVariableNames::usage="GetChangeBaseVariableNames[startbv,startnbv,goalbv,goalnbv] gives a set of pivots (variable pairs) which transfers the start to the goal.";
GetChangeBaseVariableNames[startbv_?VectorQ,startnbv_?VectorQ,goalbv_?VectorQ,goalnbv_?VectorQ]:=
	{Intersection[startbv,goalnbv],Intersection[startnbv,goalbv]}

MakeSequence::usage="MakeSequence[dic_?MatrixQ,bv_?VectorQ,nbv_?VectorQ,bases_?MatrixQ] returns pivot sequence.";
MakeSequence[origdic_?MatrixQ,origbv_?VectorQ,orignbv_?VectorQ,bases_?MatrixQ]:=
	Block[{dic = origdic, bv = origbv, nbv = orignbv, bvposi, nbvposi, tmpsequence},
		(* name to position *)
		bvposi = Flatten[Map[Position[bv,#] & ,bases[[1]]]];
		nbvposi = Flatten[Map[Position[nbv,#] & ,bases[[2]]]];
		(* make all possible sequences *)
		tmpsequence = Map[Transpose[{bvposi,#}] &, Permutations[nbvposi]];
		(* choose one *)
		If[{} == tmpsequence,tmpsequence,tmpsequence[[FirstElement[# &,Map[Apply[And,Map[Not[SimpleSameQ[0,origdic[[#[[1]],#[[2]]]]]] &,#]] &,tmpsequence]]]]]
	]

ExecVEPivotSequence::usage="ExecVEPivotSequence[dic,bv,nbv,sequence] performs a sequence of pivots to {dic,bv,nbv} according to the given sequence.";
ExecVEPivotSequence[origdic_?MatrixQ,origbv_?VectorQ,orignbv_?VectorQ,sequence_?MatrixQ]:=
	Block[{dic = origdic, bv = origbv, nbv = orignbv, i},
		Do[{dic,bv,nbv} = VEPivot[dic,bv,nbv,sequence[[i,1]],sequence[[i,2]]],{i,Length[sequence]}];
		{dic,bv,nbv}
	]

InfeasibleRowQ[vec_?VectorQ]:=
	SimpleNegative[Last[vec]] && ForAllQ[Function[Not[SimplePositive[#]]],Drop[vec,-1]]

SimplePositive:=Function[SimpleNegative[-#]]

SimpleSameQ:=
	Function[( Not[SimpleNegative[#1 - #2]] && Not[SimplePositive[#1 - #2]] )]

SimpleGreater:=Function[SimplePositive[#1 - #2]]


End[(* "`Private`" *)]


Protect[VE]
Protect[VertexEnumeration]

EndPackage[]

