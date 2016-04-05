(* ::Package:: *)

(*    ============= Interface to cdd  ================     *)


VEppl::usage =  "VEppl[A,B} returns  a list  of all  vertices of  the
convex polyhedron {x|Ax<=b}"


VEppl[A_,b_]:= Module[ {inStream,outStream,mat,m,n,i,j,result,beg,end,extremes,vertices},
               inStream = OpenTemporary[];
               outStream = OpenTemporary[];
           (* H-representation format for input to lcdd *)
               mat=Transpose[Prepend[-Transpose[A],b]]; 
               {m,n}=Dimensions[mat];
               Put[OutputForm["H-representation"],OutputForm["begin"],m,n,OutputForm["rational"],inStream];
               Table[Table[Put[mat[[i,j]],inStream],{j,n}],{i,m}];
               Put[OutputForm["end"],inStream];
           (* Run ppl *)
               Run["/usr/local/Cellar/ppl/1.1/bin/ppl_lcdd --output",outStream[[1]],inStream[[1]]];
               Close[inStream];
           (* Parse output for vertices *)
               result=ReadList[outStream[[1]],Word,RecordLists->True];
               Close[outStream];
               DeleteFile[{inStream[[1]],outStream[[1]]}]; 
               {{beg}}=Position[result,{"begin"}];
               {{end}}=Position[result,{"end"}];
               extremes=Take[result,{beg+2,end-1}];
               vertices=Cases[extremes,{"1",__}];
               vertices=Map[Drop[#,1]&,ToExpression[vertices,InputForm]];
           (* Return result *)
               vertices];
