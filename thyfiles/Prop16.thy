theory Prop16
	imports Axioms Definitions Theorems
begin

theorem Prop16:
	assumes: `axioms`
		"triangle A B C"
		"bet B C D"
	shows: "ang_lt B A C A C D \<and> ang_lt C B A A C D"
proof -
	have "\<not> col A B C" sorry
	have "\<not> (A = C)"
	proof (rule ccontr)
		assume "A = C"
		have "col A B C" using col_b `axioms` `A = C` by blast
		show "False" using `col A B C` `\<not> col A B C` by blast
	qed
	hence "A \<noteq> C" by blast
	have "\<not> (B = C)"
	proof (rule ccontr)
		assume "B = C"
		have "col A B C" using col_b `axioms` `B = C` by blast
		show "False" using `col A B C` `\<not> col A B C` by blast
	qed
	hence "B \<noteq> C" by blast
	have "C \<noteq> B" using inequalitysymmetric[OF `axioms` `B \<noteq> C`] .
	obtain E where "bet A E C \<and> seg_eq E A E C" using Prop10[OF `axioms` `A \<noteq> C`]  by  blast
	have "bet A E C" using `bet A E C \<and> seg_eq E A E C` by blast
	have "\<not> (B = E)"
	proof (rule ccontr)
		assume "B = E"
		have "bet A B C" sorry
		have "col A B C" using col_b `axioms` `bet A B C` by blast
		show "False" using `col A B C` `\<not> col A B C` by blast
	qed
	hence "B \<noteq> E" by blast
	have "E \<noteq> B" using inequalitysymmetric[OF `axioms` `B \<noteq> E`] .
	obtain F where "bet B E F \<and> seg_eq E F E B" using extensionE[OF `axioms` `B \<noteq> E` `E \<noteq> B`]  by  blast
	have "seg_eq E F E B" using `bet B E F \<and> seg_eq E F E B` by blast
	have "\<not> (A = C)"
	proof (rule ccontr)
		assume "A = C"
		have "col A B C" using col_b `axioms` `A = C` by blast
		have "\<not> col A B C" using `\<not> col A B C` .
		show "False" using `\<not> col A B C` `col A B C` by blast
	qed
	hence "A \<noteq> C" by blast
	have "C \<noteq> A" using inequalitysymmetric[OF `axioms` `A \<noteq> C`] .
	have "E \<noteq> C" using betweennotequal[OF `axioms` `bet A E C`] by blast
	obtain G where "bet A C G \<and> seg_eq C G E C" using extensionE[OF `axioms` `A \<noteq> C` `E \<noteq> C`]  by  blast
	have "\<not> (col B E A)"
	proof (rule ccontr)
		assume "col B E A"
		have "col A E C" using col_b `axioms` `bet A E C \<and> seg_eq E A E C` by blast
		have "col E A B" using collinearorder[OF `axioms` `col B E A`] by blast
		have "col E A C" using collinearorder[OF `axioms` `col A E C`] by blast
		have "A \<noteq> E" using betweennotequal[OF `axioms` `bet A E C`] by blast
		have "E \<noteq> A" using inequalitysymmetric[OF `axioms` `A \<noteq> E`] .
		have "col A B C" using collinear4[OF `axioms` `col E A B` `col E A C` `E \<noteq> A`] .
		show "False" using `col A B C` `\<not> col A B C` by blast
	qed
	hence "\<not> col B E A" by blast
	have "bet A E C" using `bet A E C` .
	have "bet B E F" using `bet B E F \<and> seg_eq E F E B` by blast
	have "ang_eq B E A C E F" using Prop15[OF `axioms` `bet B E F` `bet A E C` `\<not> col B E A`] by blast
	have "\<not> (col A E B)"
	proof (rule ccontr)
		assume "col A E B"
		have "col B E A" using collinearorder[OF `axioms` `col A E B`] by blast
		show "False" using `col B E A` `\<not> col B E A` by blast
	qed
	hence "\<not> col A E B" by blast
	have "ang_eq A E B B E A" using ABCequalsCBA[OF `axioms` `\<not> col A E B`] .
	have "ang_eq A E B C E F" using equalanglestransitive[OF `axioms` `ang_eq A E B B E A` `ang_eq B E A C E F`] .
	have "seg_eq B E F E" using doublereverse[OF `axioms` `seg_eq E F E B`] by blast
	have "seg_eq E B E F" using congruenceflip[OF `axioms` `seg_eq B E F E`] by blast
	have "\<not> (col E A B)"
	proof (rule ccontr)
		assume "col E A B"
		have "col B E A" using collinearorder[OF `axioms` `col E A B`] by blast
		show "False" using `col B E A` `\<not> col B E A` by blast
	qed
	hence "\<not> col E A B" by blast
	have "seg_eq E A E C" using `bet A E C \<and> seg_eq E A E C` by blast
	have "seg_eq E B E F" using `seg_eq E B E F` .
	have "ang_eq A E B C E F" using `ang_eq A E B C E F` .
	have "seg_eq A B C F \<and> ang_eq E A B E C F \<and> ang_eq E B A E F C" using Prop04[OF `axioms` `seg_eq E A E C` `seg_eq E B E F` `ang_eq A E B C E F`] .
	have "ang_eq E A B E C F" using `seg_eq A B C F \<and> ang_eq E A B E C F \<and> ang_eq E B A E F C` by blast
	have "\<not> (col B A E)"
	proof (rule ccontr)
		assume "col B A E"
		have "col E A B" using collinearorder[OF `axioms` `col B A E`] by blast
		show "False" using `col E A B` `\<not> col E A B` by blast
	qed
	hence "\<not> col B A E" by blast
	have "ray_on A C E" using ray4 `axioms` `bet A E C \<and> seg_eq E A E C` `A \<noteq> C` by blast
	have "B = B" using equalityreflexiveE[OF `axioms`] .
	have "A \<noteq> B" using angledistinct[OF `axioms` `ang_eq A E B B E A`] by blast
	have "B \<noteq> A" using inequalitysymmetric[OF `axioms` `A \<noteq> B`] .
	have "ray_on A B B" using ray4 `axioms` `B = B` `A \<noteq> B` by blast
	have "\<not> (col B A C)"
	proof (rule ccontr)
		assume "col B A C"
		have "col A B C" using collinearorder[OF `axioms` `col B A C`] by blast
		show "False" using `col A B C` `\<not> col A B C` by blast
	qed
	hence "\<not> col B A C" by blast
	have "ang_eq B A C B A C" using equalanglesreflexive[OF `axioms` `\<not> col B A C`] .
	have "ang_eq B A C B A E" using equalangleshelper[OF `axioms` `ang_eq B A C B A C` `ray_on A B B` `ray_on A C E`] .
	have "ang_eq B A E E A B" using ABCequalsCBA[OF `axioms` `\<not> col B A E`] .
	have "ang_eq B A C E A B" using equalanglestransitive[OF `axioms` `ang_eq B A C B A E` `ang_eq B A E E A B`] .
	have "ang_eq B A C E C F" using equalanglestransitive[OF `axioms` `ang_eq B A C E A B` `ang_eq E A B E C F`] .
	have "bet C E A" using betweennesssymmetryE[OF `axioms` `bet A E C`] .
	have "C \<noteq> E" using betweennotequal[OF `axioms` `bet C E A`] by blast
	have "ray_on C E A" using ray4 `axioms` `bet C E A` `C \<noteq> E` by blast
	have "F = F" using equalityreflexiveE[OF `axioms`] .
	have "\<not> (col E C F)"
	proof (rule ccontr)
		assume "col E C F"
		have "col B E F" using col_b `axioms` `bet B E F \<and> seg_eq E F E B` by blast
		have "col F E B" using collinearorder[OF `axioms` `col B E F`] by blast
		have "col F E C" using collinearorder[OF `axioms` `col E C F`] by blast
		have "E \<noteq> F" using betweennotequal[OF `axioms` `bet B E F`] by blast
		have "F \<noteq> E" using inequalitysymmetric[OF `axioms` `E \<noteq> F`] .
		have "col E B C" using collinear4[OF `axioms` `col F E B` `col F E C` `F \<noteq> E`] .
		have "col A E C" using col_b `axioms` `bet A E C \<and> seg_eq E A E C` by blast
		have "col E C B" using collinearorder[OF `axioms` `col E B C`] by blast
		have "col E C A" using collinearorder[OF `axioms` `col A E C`] by blast
		have "E \<noteq> C" using betweennotequal[OF `axioms` `bet A E C`] by blast
		have "col C B A" using collinear4[OF `axioms` `col E C B` `col E C A` `E \<noteq> C`] .
		have "col A B C" using collinearorder[OF `axioms` `col C B A`] by blast
		show "False" using `col A B C` `\<not> col A B C` by blast
	qed
	hence "\<not> col E C F" by blast
	have "\<not> (C = F)"
	proof (rule ccontr)
		assume "C = F"
		have "col E C F" using col_b `axioms` `C = F` by blast
		show "False" using `col E C F` `\<not> col E C F` by blast
	qed
	hence "C \<noteq> F" by blast
	have "ray_on C F F" using ray4 `axioms` `F = F` `C \<noteq> F` by blast
	have "ang_eq E C F E C F" using equalanglesreflexive[OF `axioms` `\<not> col E C F`] .
	have "ang_eq E C F A C F" using equalangleshelper[OF `axioms` `ang_eq E C F E C F` `ray_on C E A` `ray_on C F F`] .
	have "ang_eq B A C A C F" using equalanglestransitive[OF `axioms` `ang_eq B A C E C F` `ang_eq E C F A C F`] .
	have "bet B C D" using `bet B C D` .
	have "bet D C B" using betweennesssymmetryE[OF `axioms` `bet B C D`] .
	have "bet B E F" using `bet B E F` .
	have "bet F E B" using betweennesssymmetryE[OF `axioms` `bet B E F`] .
	have "\<not> (col D B F)"
	proof (rule ccontr)
		assume "col D B F"
		have "col F B D" using collinearorder[OF `axioms` `col D B F`] by blast
		have "col B E F" using col_b `axioms` `bet B E F \<and> seg_eq E F E B` by blast
		have "col F B E" using collinearorder[OF `axioms` `col B E F`] by blast
		have "B \<noteq> F" using betweennotequal[OF `axioms` `bet B E F`] by blast
		have "F \<noteq> B" using inequalitysymmetric[OF `axioms` `B \<noteq> F`] .
		have "col B D E" using collinear4[OF `axioms` `col F B D` `col F B E` `F \<noteq> B`] .
		have "col D B E" using collinearorder[OF `axioms` `col B D E`] by blast
		have "col B C D" using col_b `axioms` `bet B C D` by blast
		have "col D B C" using collinearorder[OF `axioms` `col B C D`] by blast
		have "B \<noteq> D" using betweennotequal[OF `axioms` `bet B C D`] by blast
		have "D \<noteq> B" using inequalitysymmetric[OF `axioms` `B \<noteq> D`] .
		have "col B E C" using collinear4[OF `axioms` `col D B E` `col D B C` `D \<noteq> B`] .
		have "col E C B" using collinearorder[OF `axioms` `col B E C`] by blast
		have "col A E C" using col_b `axioms` `bet A E C \<and> seg_eq E A E C` by blast
		have "col E C A" using collinearorder[OF `axioms` `col A E C`] by blast
		have "E \<noteq> C" using betweennotequal[OF `axioms` `bet A E C`] by blast
		have "col C B A" using collinear4[OF `axioms` `col E C B` `col E C A` `E \<noteq> C`] .
		have "col A B C" using collinearorder[OF `axioms` `col C B A`] by blast
		have "\<not> col A B C" using `\<not> col A B C` .
		show "False" using `\<not> col A B C` `col A B C` by blast
	qed
	hence "\<not> col D B F" by blast
	obtain H where "bet D H E \<and> bet F H C" using Pasch-innerE[OF `axioms` `bet D C B` `bet F E B` `\<not> col D B F`]  by  blast
	have "bet D H E" using `bet D H E \<and> bet F H C` by blast
	have "bet F H C" using `bet D H E \<and> bet F H C` by blast
	have "bet C H F" using betweennesssymmetryE[OF `axioms` `bet F H C`] .
	have "ray_on C F H" using ray4 `axioms` `bet C H F` `C \<noteq> F` by blast
	have "A = A" using equalityreflexiveE[OF `axioms`] .
	have "ray_on C A A" using ray4 `axioms` `A = A` `C \<noteq> A` by blast
	have "ang_eq B A C A C H" using equalangleshelper[OF `axioms` `ang_eq B A C A C F` `ray_on C A A` `ray_on C F H`] .
	have "ang_eq B A C A C F" using equalangleshelper[OF `axioms` `ang_eq B A C A C F` `ray_on C A A` `ray_on C F F`] .
	have "bet E H D" using betweennesssymmetryE[OF `axioms` `bet D H E`] .
	have "ray_on C A E" using ray5[OF `axioms` `ray_on C E A`] .
	have "D = D" using equalityreflexiveE[OF `axioms`] .
	have "D \<noteq> C" using betweennotequal[OF `axioms` `bet D C B`] by blast
	have "C \<noteq> D" using inequalitysymmetric[OF `axioms` `D \<noteq> C`] .
	have "ray_on C D D" using ray4 `axioms` `D = D` `C \<noteq> D` by blast
	have "ang_eq B A C A C H" using equalanglestransitive[OF `axioms` `ang_eq B A C B A C` `ang_eq B A C A C H`] .
	have "ang_lt B A C A C D" sorry
	have "B \<noteq> C" using betweennotequal[OF `axioms` `bet B C D`] by blast
	obtain e where "bet B e C \<and> seg_eq e B e C" using Prop10[OF `axioms` `B \<noteq> C`]  by  blast
	have "bet B e C" using `bet B e C \<and> seg_eq e B e C` by blast
	have "col B e C" using col_b `axioms` `bet B e C \<and> seg_eq e B e C` by blast
	have "\<not> (A = e)"
	proof (rule ccontr)
		assume "A = e"
		have "bet B A C" sorry
		have "col B A C" using col_b `axioms` `bet B A C` by blast
		show "False" using `col B A C` `\<not> col B A C` by blast
	qed
	hence "A \<noteq> e" by blast
	have "e \<noteq> A" using inequalitysymmetric[OF `axioms` `A \<noteq> e`] .
	obtain f where "bet A e f \<and> seg_eq e f e A" using extensionE[OF `axioms` `A \<noteq> e` `e \<noteq> A`]  by  blast
	have "seg_eq e f e A" using `bet A e f \<and> seg_eq e f e A` by blast
	have "\<not> (B = C)"
	proof (rule ccontr)
		assume "B = C"
		have "col B A C" using col_b `axioms` `B = C` by blast
		have "\<not> col B A C" using `\<not> col B A C` .
		show "False" using `\<not> col B A C` `col B A C` by blast
	qed
	hence "B \<noteq> C" by blast
	have "\<not> (col A e B)"
	proof (rule ccontr)
		assume "col A e B"
		have "col B e C" using col_b `axioms` `bet B e C \<and> seg_eq e B e C` by blast
		have "col e B A" using collinearorder[OF `axioms` `col A e B`] by blast
		have "col e B C" using collinearorder[OF `axioms` `col B e C`] by blast
		have "B \<noteq> e" using betweennotequal[OF `axioms` `bet B e C`] by blast
		have "e \<noteq> B" using inequalitysymmetric[OF `axioms` `B \<noteq> e`] .
		have "col B A C" using collinear4[OF `axioms` `col e B A` `col e B C` `e \<noteq> B`] .
		show "False" using `col B A C` `\<not> col B A C` by blast
	qed
	hence "\<not> col A e B" by blast
	have "bet B e C" using `bet B e C` .
	have "bet A e f" using `bet A e f \<and> seg_eq e f e A` by blast
	have "ang_eq A e B C e f" using Prop15[OF `axioms` `bet A e f` `bet B e C` `\<not> col A e B`] by blast
	have "\<not> (col B e A)"
	proof (rule ccontr)
		assume "col B e A"
		have "col A e B" using collinearorder[OF `axioms` `col B e A`] by blast
		show "False" using `col A e B` `\<not> col A e B` by blast
	qed
	hence "\<not> col B e A" by blast
	have "ang_eq B e A A e B" using ABCequalsCBA[OF `axioms` `\<not> col B e A`] .
	have "ang_eq B e A C e f" using equalanglestransitive[OF `axioms` `ang_eq B e A A e B` `ang_eq A e B C e f`] .
	have "seg_eq A e f e" using doublereverse[OF `axioms` `seg_eq e f e A`] by blast
	have "seg_eq e A e f" using congruenceflip[OF `axioms` `seg_eq A e f e`] by blast
	have "\<not> (col e B A)"
	proof (rule ccontr)
		assume "col e B A"
		have "col A e B" using collinearorder[OF `axioms` `col e B A`] by blast
		show "False" using `col A e B` `\<not> col A e B` by blast
	qed
	hence "\<not> col e B A" by blast
	have "seg_eq e B e C" using `bet B e C \<and> seg_eq e B e C` by blast
	have "seg_eq e A e f" using `seg_eq e A e f` .
	have "ang_eq B e A C e f" using `ang_eq B e A C e f` .
	have "seg_eq B A C f \<and> ang_eq e B A e C f \<and> ang_eq e A B e f C" using Prop04[OF `axioms` `seg_eq e B e C` `seg_eq e A e f` `ang_eq B e A C e f`] .
	have "ang_eq e B A e C f" using `seg_eq B A C f \<and> ang_eq e B A e C f \<and> ang_eq e A B e f C` by blast
	have "\<not> (col A B e)"
	proof (rule ccontr)
		assume "col A B e"
		have "col e B A" using collinearorder[OF `axioms` `col A B e`] by blast
		show "False" using `col e B A` `\<not> col e B A` by blast
	qed
	hence "\<not> col A B e" by blast
	have "ray_on B C e" using ray4 `axioms` `bet B e C \<and> seg_eq e B e C` `B \<noteq> C` by blast
	have "ray_on B A A" using ray4 `axioms` `A = A` `B \<noteq> A` by blast
	have "\<not> (col A B C)"
	proof (rule ccontr)
		assume "col A B C"
		have "col B A C" using collinearorder[OF `axioms` `col A B C`] by blast
		show "False" using `col B A C` `\<not> col B A C` by blast
	qed
	hence "\<not> col A B C" by blast
	have "ang_eq A B C A B C" using equalanglesreflexive[OF `axioms` `\<not> col A B C`] .
	have "ang_eq A B C A B e" using equalangleshelper[OF `axioms` `ang_eq A B C A B C` `ray_on B A A` `ray_on B C e`] .
	have "ang_eq A B e e B A" using ABCequalsCBA[OF `axioms` `\<not> col A B e`] .
	have "ang_eq A B C e B A" using equalanglestransitive[OF `axioms` `ang_eq A B C A B e` `ang_eq A B e e B A`] .
	have "ang_eq A B C e C f" using equalanglestransitive[OF `axioms` `ang_eq A B C e B A` `ang_eq e B A e C f`] .
	have "bet C e B" using betweennesssymmetryE[OF `axioms` `bet B e C`] .
	have "C \<noteq> e" using betweennotequal[OF `axioms` `bet C e B`] by blast
	have "ray_on C e B" using ray4 `axioms` `bet C e B` `C \<noteq> e` by blast
	have "f = f" using equalityreflexiveE[OF `axioms`] .
	have "\<not> col e C f" using equalanglesNC[OF `axioms` `ang_eq A B C e C f`] .
	have "\<not> (C = f)"
	proof (rule ccontr)
		assume "C = f"
		have "col e C f" using col_b `axioms` `C = f` by blast
		show "False" using `col e C f` `\<not> col e C f` by blast
	qed
	hence "C \<noteq> f" by blast
	have "ray_on C f f" using ray4 `axioms` `f = f` `C \<noteq> f` by blast
	have "\<not> (col e C f)"
	proof (rule ccontr)
		assume "col e C f"
		have "col A e f" using col_b `axioms` `bet A e f \<and> seg_eq e f e A` by blast
		have "col f e A" using collinearorder[OF `axioms` `col A e f`] by blast
		have "col f e C" using collinearorder[OF `axioms` `col e C f`] by blast
		have "e \<noteq> f" using betweennotequal[OF `axioms` `bet A e f`] by blast
		have "f \<noteq> e" using inequalitysymmetric[OF `axioms` `e \<noteq> f`] .
		have "col e A C" using collinear4[OF `axioms` `col f e A` `col f e C` `f \<noteq> e`] .
		have "col e C A" using collinearorder[OF `axioms` `col e A C`] by blast
		have "col e C B" using collinearorder[OF `axioms` `col B e C`] by blast
		have "e \<noteq> C" using betweennotequal[OF `axioms` `bet B e C`] by blast
		have "col C A B" using collinear4[OF `axioms` `col e C A` `col e C B` `e \<noteq> C`] .
		have "col B A C" using collinearorder[OF `axioms` `col C A B`] by blast
		show "False" using `col B A C` `\<not> col B A C` by blast
	qed
	hence "\<not> col e C f" by blast
	have "ang_eq e C f e C f" using equalanglesreflexive[OF `axioms` `\<not> col e C f`] .
	have "ang_eq e C f B C f" using equalangleshelper[OF `axioms` `ang_eq e C f e C f` `ray_on C e B` `ray_on C f f`] .
	have "ang_eq A B C B C f" using equalanglestransitive[OF `axioms` `ang_eq A B C e C f` `ang_eq e C f B C f`] .
	have "bet A C G" using `bet A C G \<and> seg_eq C G E C` by blast
	have "bet G C A" using betweennesssymmetryE[OF `axioms` `bet A C G`] .
	have "G \<noteq> C" using betweennotequal[OF `axioms` `bet G C A`] by blast
	have "C \<noteq> G" using inequalitysymmetric[OF `axioms` `G \<noteq> C`] .
	have "bet A e f" using `bet A e f` .
	have "bet f e A" using betweennesssymmetryE[OF `axioms` `bet A e f`] .
	have "\<not> (col G A f)"
	proof (rule ccontr)
		assume "col G A f"
		have "col f A G" using collinearorder[OF `axioms` `col G A f`] by blast
		have "col A e f" using col_b `axioms` `bet A e f \<and> seg_eq e f e A` by blast
		have "col f A e" using collinearorder[OF `axioms` `col A e f`] by blast
		have "A \<noteq> f" using betweennotequal[OF `axioms` `bet A e f`] by blast
		have "f \<noteq> A" using inequalitysymmetric[OF `axioms` `A \<noteq> f`] .
		have "col A G e" using collinear4[OF `axioms` `col f A G` `col f A e` `f \<noteq> A`] .
		have "col G A e" using collinearorder[OF `axioms` `col A G e`] by blast
		have "col A C G" using col_b `axioms` `bet A C G \<and> seg_eq C G E C` by blast
		have "col G A C" using collinearorder[OF `axioms` `col A C G`] by blast
		have "A \<noteq> G" using betweennotequal[OF `axioms` `bet A C G`] by blast
		have "G \<noteq> A" using inequalitysymmetric[OF `axioms` `A \<noteq> G`] .
		have "col A e C" using collinear4[OF `axioms` `col G A e` `col G A C` `G \<noteq> A`] .
		have "col e C A" using collinearorder[OF `axioms` `col A e C`] by blast
		have "col B e C" using col_b `axioms` `bet B e C \<and> seg_eq e B e C` by blast
		have "col e C B" using collinearorder[OF `axioms` `col B e C`] by blast
		have "e \<noteq> C" using betweennotequal[OF `axioms` `bet B e C`] by blast
		have "col C A B" using collinear4[OF `axioms` `col e C A` `col e C B` `e \<noteq> C`] .
		have "col A B C" using collinearorder[OF `axioms` `col C A B`] by blast
		have "\<not> col A B C" using `\<not> col A B C` .
		show "False" using `\<not> col A B C` `col A B C` by blast
	qed
	hence "\<not> col G A f" by blast
	obtain h where "bet G h e \<and> bet f h C" using Pasch-innerE[OF `axioms` `bet G C A` `bet f e A` `\<not> col G A f`]  by  blast
	have "bet G h e" using `bet G h e \<and> bet f h C` by blast
	have "bet f h C" using `bet G h e \<and> bet f h C` by blast
	have "bet C h f" using betweennesssymmetryE[OF `axioms` `bet f h C`] .
	have "h \<noteq> C" using betweennotequal[OF `axioms` `bet f h C`] by blast
	have "C \<noteq> h" using inequalitysymmetric[OF `axioms` `h \<noteq> C`] .
	have "ray_on C h f" using ray4 `axioms` `bet C h f` `C \<noteq> h` by blast
	have "ray_on C f h" using ray5[OF `axioms` `ray_on C h f`] .
	have "ray_on C B B" using ray4 `axioms` `B = B` `C \<noteq> B` by blast
	have "ang_eq A B C B C h" using equalangleshelper[OF `axioms` `ang_eq A B C B C f` `ray_on C B B` `ray_on C f h`] .
	have "ang_eq A B C B C f" using equalangleshelper[OF `axioms` `ang_eq A B C B C f` `ray_on C B B` `ray_on C f f`] .
	have "bet e h G" using betweennesssymmetryE[OF `axioms` `bet G h e`] .
	have "bet C e B" using betweennesssymmetryE[OF `axioms` `bet B e C`] .
	have "ray_on C e B" using ray4 `axioms` `bet C e B` `C \<noteq> e` by blast
	have "ray_on C B e" using ray5[OF `axioms` `ray_on C e B`] .
	have "G = G" using equalityreflexiveE[OF `axioms`] .
	have "ray_on C G G" using ray4 `axioms` `G = G` `C \<noteq> G` by blast
	have "ang_eq A B C B C h" using equalanglestransitive[OF `axioms` `ang_eq A B C A B C` `ang_eq A B C B C h`] .
	have "ang_lt A B C B C G" sorry
	have "\<not> (col G C B)"
	proof (rule ccontr)
		assume "col G C B"
		have "col A C G" using col_b `axioms` `bet A C G \<and> seg_eq C G E C` by blast
		have "col G C A" using collinearorder[OF `axioms` `col A C G`] by blast
		have "C \<noteq> G" using betweennotequal[OF `axioms` `bet A C G`] by blast
		have "G \<noteq> C" using inequalitysymmetric[OF `axioms` `C \<noteq> G`] .
		have "col C B A" using collinear4[OF `axioms` `col G C B` `col G C A` `G \<noteq> C`] .
		have "col A B C" using collinearorder[OF `axioms` `col C B A`] by blast
		show "False" using `col A B C` `\<not> col A B C` by blast
	qed
	hence "\<not> col G C B" by blast
	have "ang_eq G C B D C A" using Prop15[OF `axioms` `bet G C A` `bet B C D` `\<not> col G C B`] by blast
	have "\<not> (col A C D)"
	proof (rule ccontr)
		assume "col A C D"
		have "col D C A" using collinearorder[OF `axioms` `col A C D`] by blast
		have "col B C D" using col_b `axioms` `bet B C D` by blast
		have "col D C B" using collinearorder[OF `axioms` `col B C D`] by blast
		have "C \<noteq> D" using betweennotequal[OF `axioms` `bet B C D`] by blast
		have "D \<noteq> C" using inequalitysymmetric[OF `axioms` `C \<noteq> D`] .
		have "col C A B" using collinear4[OF `axioms` `col D C A` `col D C B` `D \<noteq> C`] .
		have "col A B C" using collinearorder[OF `axioms` `col C A B`] by blast
		show "False" using `col A B C` `\<not> col A B C` by blast
	qed
	hence "\<not> col A C D" by blast
	have "ang_eq G C B B C G" using ABCequalsCBA[OF `axioms` `\<not> col G C B`] .
	have "ang_lt A B C G C B" using angleorderrespectscongruence[OF `axioms` `ang_lt A B C B C G` `ang_eq G C B B C G`] .
	have "\<not> (col D C A)"
	proof (rule ccontr)
		assume "col D C A"
		have "col A C D" using collinearorder[OF `axioms` `col D C A`] by blast
		show "False" using `col A C D` `\<not> col A C D` by blast
	qed
	hence "\<not> col D C A" by blast
	have "ang_eq D C A A C D" using ABCequalsCBA[OF `axioms` `\<not> col D C A`] .
	have "ang_eq G C B A C D" using equalanglestransitive[OF `axioms` `ang_eq G C B D C A` `ang_eq D C A A C D`] .
	have "ang_eq A C D G C B" using equalanglessymmetric[OF `axioms` `ang_eq G C B A C D`] .
	have "ang_lt A B C G C B" using `ang_lt A B C G C B` .
	have "ang_lt A B C A C D" using angleorderrespectscongruence[OF `axioms` `ang_lt A B C G C B` `ang_eq A C D G C B`] .
	have "\<not> (col C B A)"
	proof (rule ccontr)
		assume "col C B A"
		have "col A B C" using collinearorder[OF `axioms` `col C B A`] by blast
		show "False" using `col A B C` `\<not> col A B C` by blast
	qed
	hence "\<not> col C B A" by blast
	have "ang_eq C B A A B C" using ABCequalsCBA[OF `axioms` `\<not> col C B A`] .
	have "ang_lt C B A A C D" using angleorderrespectscongruence2[OF `axioms` `ang_lt A B C A C D` `ang_eq C B A A B C`] .
	have "ang_lt B A C A C D \<and> ang_lt C B A A C D" using `ang_lt B A C A C D` `ang_lt C B A A C D` by blast
	thus ?thesis by blast
qed

end