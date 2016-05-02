(* ::Package:: *)

GaleShapleyAlgorithm[g_Graph,pref_List]:=Module[{vc,cel,cpref,mpref,wpref,proposals,rejects},
	If[Not@BipartiteGraphQ[g],Return["Not bipartite graph"]];
	vc=VertexCount@g;
	cel=Sort/@EdgeList@g;
	cpref=Map[Sort,pref,{2}];
	rejects=EdgeList@g;
	While[rejects!={},
	mpref=Part[cpref,1;;vc/2]; (*This part is sensitive to the preference list provided*)
	wpref=Part[cpref,(vc/2+1);;vc]; (*The same with above*)
	proposals=Propose[mpref];
	rejects=Reject[wpref,proposals];
	If[rejects=={},Return@proposals];
	cpref=UpdatePreference[cpref,rejects];
	Print@proposals; Print@rejects; Print@Column@cpref;]];


Propose[ppref_List]:=First/@ppref;

Reject[rpref_List,prop_List]:=Module[{conflicts,Rejects},
	conflicts=Select[IncidenceList[Graph@prop,#]&/@VertexList[Graph@prop],Length[#]>1&];
	If[conflicts=={},Return[{}]];
	Rejects[l_,subl_]:=DeleteCases[subl,_?(SameQ[Position[l,#][[1]][[1]],Min@@Flatten@@{Position[l,#]&/@subl}]&)];
	Flatten[Rejects@@@Select[Gather[Join[rpref,conflicts],IntersectingQ],Length[#]>1&]]];
(*
Reject[rpref_List,prop_List]:=Module[{subg,conflicts,subpref,ListPosition,conflictindices},
	subg=Graph[prop];
	conflicts=Select[IncidenceList[subg,#]&/@VertexList[subg],Length[#]>1&];
	If[conflicts=={},Return[{}]];
	subpref=Select[rpref,IntersectingQ[#,Flatten@conflicts]&];
	ListPosition=Flatten@Position[#1,Alternatives@@#2]&;
	conflictindices=ListPosition@@@Gather[Join[subpref,conflicts],IntersectingQ];
	Flatten[Part@@@Transpose@Join[{subpref},{Drop[#,1]&/@Sort/@conflictindices}]]];
*)
UpdatePreference[pref_List,rej_List]:=Fold[DeleteCases,#,rej]&/@pref;


CompleteBipartiteGraph[i_Integer]:=CompleteGraph[{i,i}]
