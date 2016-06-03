(* ::Package:: *)

(* directg or watercluster2 *)
(* We do NOT use str=Import[outStream[[1]],"Table"] because Import[] is extremely slow. *)


(* g could be a graph or a list of graphs *)
NTOrientations[g_]:= Module[{inStream,outStream,str},
	inStream=OpenTemporary[];
	outStream=OpenTemporary[];
	Export[inStream,g,"Graph6"];
	(* Run directg *)
	Run["/usr/local/Cellar/nauty/26r5/bin/directg -o -T",inStream[[1]],outStream[[1]]];
	Close[inStream];
	str=ReadList[outStream[[1]],Number,RecordLists->True];
	Close[outStream];
	DeleteFile[{inStream[[1]],outStream[[1]]}];
	str=Drop[#,2]&/@str;
	Graph[DirectedEdge@@@Partition[#,2]]&/@str];


(* g could be a graph or a list of graphs *)
NTSuperOrientations[g_]:= Module[{inStream,outStream,str},
	inStream=OpenTemporary[];
	outStream=OpenTemporary[];
	Export[inStream,g,"Graph6"];
	(* Run directg *)
	Run["/usr/local/Cellar/nauty/26r5/bin/directg -T",inStream[[1]],outStream[[1]]];
	Close[inStream];
	str=ReadList[outStream[[1]],Number,RecordLists->True];
	Close[outStream];
	DeleteFile[{inStream[[1]],outStream[[1]]}];
	str=Drop[#,2]&/@str;
	Graph[DirectedEdge@@@Partition[#,2]]&/@str];


(* gentourng *)


NTTournaments[n_Integer]:= Module[{outStream,str,adjlist},
	outStream = OpenTemporary[];
	(* Run gentourng *)
	Run["/usr/local/Cellar/nauty/26r5/bin/gentourng ",n,outStream[[1]]];
	str=ReadList[outStream[[1]],String];
	Close[outStream];
	DeleteFile[{outStream[[1]]}];
	str=ToExpression@StringCases[#,DigitCharacter]&/@str;
	adjlist=gentourngAdjacencyMatrix/@str;
	AdjacencyGraph/@adjlist];


gentourngAdjacencyMatrix[l_List]:=Module[{n,mat,auxmat},
	n=Abs[1/2 (1-Sqrt[1+8*Length@l])];
	mat=SparseArray[Rule[#1,#2]&@@@Thread@{Flatten[Table[{i,j+1},{i,n},{j,i,n}],1],l}];
	mat=Append[mat,ConstantArray[0,n+1]];
	auxmat=SparseArray[{i_,j_}/;i<j->1,{n+1,n+1}];mat+Transpose[auxmat-mat]];
