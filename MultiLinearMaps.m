(* ::Package:: *)

(* ::Subsubsection:: *)
(*Prologue*)


BeginPackage["MultiLinearMaps`"];


Unprotect[MapDict,System,AtomicSpace,VecSpace,IndexDict,MultiMap];
(* Unprotect[Name,Dimension,Type]; 
Unprotect[AtomNames,AtomicQ,AtomDimensions,Atoms,Atomize]; *)
Unprotect[SystemMapping];
Unprotect[Matrixize,Canonicalize];
Unprotect[AddMaps,ComposeMaps];
Unprotect[PartialTrace,MapTranspose,Adjoint,PartialTranspose];
Unprotect[basisElement,basisKet,basisBra];
Unprotect[OmegaKet,OmegaBra,OmegaOp];
Unprotect[fromMatrix];
Unprotect[Swap];


ContractableSystems::usage="ContractableSystem[L,R] returns the system names that are contractable in the composition L \[EmptySmallCircle] R. Input MapDicts.";


ComposeMaps::usage="Returns an object describing the composition L \[EmptySmallCircle] R. For MapDict inputs, a MapDict. For MultiMap inputs, a MultiMap.";


ValidMappingQ::usage="";
ComposableQ::usage="";
MappingEqualQ::usage="";
ContractableSystemsQ::usage="";


(* Name::usage="Name[x] returns the name of x, a String";
Dimension::usage="Dimension[x] returns the dimension of x, an Integer. If x is a VecSpace object, the dimension of the tensor product space.";
Type::usage="Type[x] gives the type of x, either \"ket\" or \"bra\""; *)


(* AtomNames::usage="";
AtomicQ::usage="";
AtomDimensions::usage="";
Atoms::usage="";
Atomize::usage=""; *)


ComposeMaps::inputs = "Input maps are not composable in this order.";


Begin["`Private`"];



(* ::Subsubsection:: *)
(*MapDict *)


ContractableSystems[L_MapDict,R_MapDict]:=Intersection[L[[2]],R[[1]]];


rawComposeMaps[L_MapDict,R_MapDict]:=
MapDict@@({Join[L[[1]],Complement[R[[1]],#]],Join[R[[2]],Complement[L[[2]],#]]}&[ContractableSystems[L,R]]);


NonCommutativeMultiply[MapDict[oL_,iL_],MapDict[oR_,iR_]]^:=ComposeMaps[MapDict[oL,iL],MapDict[oR,iR]]


ValidMappingQ[x_MapDict]:=And@@(DuplicateFreeQ/@x);
ComposableQ[L_MapDict,R_MapDict]:=ValidMappingQ[ComposeMaps[L,R]];
MappingEqualQ[x_MapDict,y_MapDict]:=Equal@@(Sort/@#&/@{x,y});


ComposeMaps[L_MapDict,R_MapDict]:=Module[{cmp=rawComposeMaps[L,R]},If[ValidMappingQ[cmp],cmp,Message[ComposeMaps::inputs]]];


ContractableSystems[x_MapDict]:=
ContractableSystems[x,x]; 
ContractableSystemQ[x_MapDict,sysname_]:=And@@(MemberQ[#,sysname]&/@x);
ContractableSystemsQ[x_MapDict,sysnames_List]:=And@@(SubsetQ[#,sysnames]&/@x);


(* ::Subsubsection:: *)
(*System*)


Name[x_System]:=x[[1]];
Dimension[x_System]:=x[[2]];


(* ::Subsubsection:: *)
(*AtomicSpace*)


Name[x_AtomicSpace]:=Name[x[[1]]]
Dimension[x_AtomicSpace]:=Dimension[x[[1]]];
Type[x_AtomicSpace]:=x[[2]];


(* ::Subsubsection:: *)
(*VecSpace*)


AtomNames[x_VecSpace]:=Level[x,{3}][[;;;;2]];
AtomicQ[x_VecSpace]:=Length[x]==1;
AtomDimensions[x_VecSpace]:=Level[x,{3}][[2;;;;2]];
Dimension[x_VecSpace]:=Times@@AtomDimensions[x];


(* ::Subsubsection:: *)
(*IndexDict*)


Atoms[x_IndexDict]:=Level[x,{2}];
Atomize[x_IndexDict]:=IndexDict@@(VecSpace[#1]&)/@Atoms[x];
AtomicQ[x_IndexDict]:=And@@AtomicQ/@x;
AtomNames[x_IndexDict]:=Level[x,{4}][[1;;All;;2]]


Kets[x_IndexDict]:=Select[Atoms[x],#[[2]]=="ket"&]
Bras[x_IndexDict]:=Select[Atoms[x],#[[2]]=="bra"&]


SystemMapping[x_IndexDict]:=MapDict@@(Map[Name,{Kets[x],Bras[x]},{2}]);
ValidMappingQ[x_IndexDict]:=ValidMappingQ[SystemMapping[x]];
MappingEqualQ[x_IndexDict,y_IndexDict]:=MappingEqualQ[SystemMapping[x],SystemMapping[y]];
ComposableQ[L_IndexDict,R_IndexDict]:=ComposableQ[SystemMapping@L,SystemMapping@R]


ContractableSystemQ[x_IndexDict,sysname_]:=ContractableSystemQ[SystemMapping[x],sysname];
ContractableSystemsQ[x_IndexDict,sysnames_List]:=ContractableSystemsQ[SystemMapping[x],sysnames]


NameSort[x_IndexDict/;AtomicQ[x]]:=IndexDict@@(VecSpace[#]&/@SortBy[Level[x,{2}],{Name,Type[#]=="bra"&}])
TypeSort[x_IndexDict/;AtomicQ[x]]:=IndexDict@@(VecSpace[#]&/@SortBy[Level[x,{2}],{Type[#]=="bra"&,Name}])


KetIndices[x_IndexDict]:=Flatten[Position[Atoms[x],z_/;Type[z]=="ket"]];
BraIndices[x_IndexDict]:=Flatten[Position[Atoms[x],z_/;Type[z]=="bra"]]


CompositionIndices[L_IndexDict,R_IndexDict]:=Flatten[{Position[Atoms@L,z_/;Type[z]=="bra"&&Name[z]==#],Position[Atoms@R,z_/;Type[z]=="ket"&&Name[z]==#]}]&/@(ContractableSystems@@(SystemMapping[#]&/@{L,R}));


ComposeMaps[L_IndexDict/;AtomicQ[L],R_IndexDict/;AtomicQ[R]]:=With[{ci=CompositionIndices[L,R]},
If[ci=={},IndexDict@@(Join[L,R]),IndexDict@@(Join@@MapThread[Delete,{{L,R},Transpose[{#}]&/@Transpose[ci]}])]]


ContractionIndices[x_IndexDict,sysnames_List]:=If[ContractableSystemsQ[x,sysnames],
With[{atoms=Atoms[x]},
Flatten[{Position[atoms,z_/;Type[z]=="bra"&&Name[z]==#],Position[atoms,z_/;Type[z]=="ket"&&Name[z]==#]}]&/@(sysnames)],{}]


ContractMap[x_IndexDict,sysnames_List]:=If[ContractableSystemsQ[x,sysnames],Module[{r=Select[Atoms[x],!MemberQ[sysnames,Name[#]]&]},If[r=={},IndexDict[],IndexDict[VecSpace@@r]]]]


(* ::Subsubsection:: *)
(*MultiMap*)


AtomicQ[t_MultiMap]:=And[AtomicQ[t[[1]]],List@@Dimension/@Atoms[t[[1]]]==Dimensions[t[[2]]]];Atomize[t_MultiMap]:=
If[AtomicQ[t],t,
Module[{atomdict=Atomize[t[[1]]]},
MultiMap@@{atomdict,ArrayReshape[t[[2]],List@@Dimension/@atomdict]}]];


ComposableQ[L_MultiMap,R_MultiMap]:=ComposableQ[L[[1]],R[[1]]];
SystemMappingEqualQ[t1_MultiMap,t2_MultiMap]:=MappingEqualQ[t1[[1]],t2[[1]]]; 


ComposeAtomicTensors[L_MultiMap,R_MultiMap]:=If[ComposableQ[L[[1]],R[[1]]],MultiMap@@{ComposeMaps[L[[1]],R[[1]]],Activate[TensorContract[Inactive[TensorProduct][L[[2]],R[[2]]],(#+{0,Length[L[[1]]]})&/@CompositionIndices[L[[1]],R[[1]]]]]}]


ComposeMaps[L_MultiMap,R_MultiMap]:=ComposeAtomicTensors[Atomize[L],Atomize[R]];
ComposeMaps[x_MultiMap]:=x;
ComposeMaps[L_MultiMap,R_MultiMap,x__MultiMap]:=ComposeMaps[ComposeMaps[L,R],ComposeMaps[x]]


SystemMapping[t_MultiMap]:=SystemMapping[t[[1]]]


Times[MultiMap[x_,y_],z_?NumericQ]^:=MultiMap[x,z y];
NonCommutativeMultiply[MultiMap[x1_,x2_],MultiMap[y1_,y2_]]^:=ComposeMaps[MultiMap[x1,x2],MultiMap[y1,y2]];


genPerm[list1_,list2_]:=Flatten[Position[list1,#]&/@list2];
SortMap[x_IndexDict/;AtomicQ[x],f_]:=genPerm[List@@(f[x]),List@@x]


Canonicalize[t_MultiMap]:=
If[Length[t[[1]]]==0,t,MultiMap@@{TypeSort[#[[1]]],Transpose[#[[2]],SortMap[#[[1]],TypeSort]]}&[Atomize[t]]];
AddMaps[t1_MultiMap,t2_MultiMap]:=If[SystemMappingEqualQ[t1,t2],Module[{ct1=Canonicalize[t1]},MultiMap[ct1[[1]],ct1[[2]]+Canonicalize[t2][[2]]]]];
Plus[MultiMap[x1_,y1_],MultiMap[x2_,y2_]]^:=AddMaps[MultiMap[x1,y1],MultiMap[x2,y2]]



Matrixize[t_MultiMap]:=
Module[{ct,keti,brai},
ct=Canonicalize[t];
keti=KetIndices[ct[[1]]];
brai=BraIndices[ct[[1]]];
Which[
keti=={}&&brai=={},
MultiMap[IndexDict[],ct[[2]]],
keti=={}||brai=={},
MultiMap[IndexDict[VecSpace@@Atoms[ct[[1]]]],Flatten[ct[[2]]]],
True,
MultiMap@@({IndexDict@@(VecSpace@@#&/@SplitBy[Atoms[ct[[1]]],Type]),Flatten[ct[[2]],{keti,brai}]})]]


(* ::Subsubsection:: *)
(*Constructors*)


basisElement[sys_System,num_,type_]:=MultiMap@@{IndexDict[VecSpace[AtomicSpace[sys,type]]],SparseArray[{num+1->1},{Dimension[sys]}]};
basisKet[sys_System,num_]:=basisElement[sys,num,"ket"];
basisBra[sys_System,num_]:=basisElement[sys,num,"bra"];


OmegaKet[sys1_System,sys2_System]:=MultiMap[IndexDict[VecSpace[AtomicSpace[sys1,"ket"]],VecSpace[AtomicSpace[sys2,"ket"]]],SparseArray@Flatten[IdentityMatrix[Dimension@sys1]]];
OmegaBra[sys1_System,sys2_System]:=MultiMap[IndexDict[VecSpace[AtomicSpace[sys1,"bra"]],VecSpace[AtomicSpace[sys2,"bra"]]],SparseArray@Flatten[IdentityMatrix[Dimension@sys1]]];
OmegaOp[sys1_System,sys2_System]:=MultiMap[IndexDict[VecSpace[AtomicSpace[sys1,"ket"],AtomicSpace[sys1,"bra"]],VecSpace[AtomicSpace[sys2,"ket"],AtomicSpace[sys2,"bra"]]],SparseArray[IdentityMatrix[(Dimension@sys1)^2]]]


Swap[sys1_System,sys2_System]:=PartialTranspose[OmegaOp[sys1,sys2],{Name[sys1]}];
Swap::usage="Swap[sys1,sys2] returns the swap operator (a MultiMap) of the two systems. Input System objects.";


fromMatrix[systems_List,matrix_]:=MultiMap[IndexDict[VecSpace@@(AtomicSpace[#,"ket"]&/@systems),VecSpace@@(AtomicSpace[#,"bra"]&/@systems)],SparseArray@matrix];
fromMatrix[sysout_List,sysin_List,matrix_]:=MultiMap[IndexDict[VecSpace@@(AtomicSpace[#,"ket"]&/@sysout),VecSpace@@(AtomicSpace[#,"bra"]&/@sysin)],SparseArray@matrix]





(* ::Subsubsection:: *)
(*Maps on MultiLinearMaps*)


(* ::Text:: *)
(*Partial Transpose*)


KetAddress[x_IndexDict,sysname_]:=Position[x,z_/;Name[z]==sysname&&Type[z]=="ket",{2}];
BraAddress[x_IndexDict,sysname_]:=Position[x,z_/;Name[z]==sysname&&Type[z]=="bra",{2}]


KetAddresses[x_IndexDict,sysnames_List]:=Position[x,z_/;MemberQ[sysnames,Name[z]]&&Type[z]=="ket",{2}];
BraAddresses[x_IndexDict,sysnames_List]:=Position[x,z_/;MemberQ[sysnames,Name[z]]&&Type[z]=="bra",{2}]


PartialTranspose[x_IndexDict,sysnames_List]:=If[ContractableSystemsQ[x,sysnames],Module[{k=Join[#,{2}]&/@KetAddresses[x,sysnames],b=Join[#,{2}]&/@BraAddresses[x,sysnames]},
ReplacePart[x,{k->"bra",b->"ket"}]]]


PartialTranspose[x_MultiMap,sysnames_List]:=MultiMap[PartialTranspose[x[[1]],sysnames],x[[2]]]


(* ::Text:: *)
(*Transpose, Adjoint*)


KetAddresses[x_IndexDict]:=Position[x,z_/;Type[z]=="ket",{2}];
BraAddresses[x_IndexDict]:=Position[x,z_/;Type[z]=="bra",{2}]


MapTranspose[x_MultiMap]:=MultiMap[Module[{k=Join[#,{2}]&/@KetAddresses[x[[1]]],b=Join[#,{2}]&/@BraAddresses[x[[1]]]},
ReplacePart[x[[1]],{k->"bra",b->"ket"}]],x[[2]]];
Transpose[MultiMap[x_,y_]]^:=MapTranspose[MultiMap[x,y]]


Adjoint[x_MultiMap]:=MultiMap[Module[{k=Join[#,{2}]&/@KetAddresses[x[[1]]],b=Join[#,{2}]&/@BraAddresses[x[[1]]]},
ReplacePart[x[[1]],{k->"bra",b->"ket"}]],Conjugate[x[[2]]]];


(* ::Text:: *)
(*Partial Trace*)


PartialTrace[x_MultiMap/;AtomicQ[x],sysnames_List]:=
If[ContractableSystemsQ[x[[1]],sysnames],MultiMap[ContractMap[x[[1]],sysnames],TensorContract[x[[2]],ContractionIndices[x[[1]],sysnames]]]]


(* ::Subsubsection:: *)
(*Epilogue*)


End[]

Protect[MapDict,System,AtomicSpace,VecSpace,IndexDict,MultiMap];
Protect[SystemMapping,Matrixize,Canonicalize,AddMaps,ComposeMaps];
Protect[PartialTrace,MapTranspose,Adjoint,PartialTranspose];
Protect[basisElement,basisKet,basisBra];
Protect[OmegaKet,OmegaBra,OmegaOp];
Protect[fromMatrix];
Protect[Swap];


EndPackage[]
