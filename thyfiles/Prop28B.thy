theory Prop28B
	imports Axioms Definitions Theorems
begin

theorem Prop28B:
	assumes: `axioms`
		"bet A G B"
		"bet C H D"
		"ang_suppl B G H G H D"
		"same_side B D G H"
	shows: "parallel A B C D"
proof -
	have "same_side D B G H" using samesidesymmetric[OF `axioms` `same_side B D G H`] by blast
	obtain a b c d e where "linear_pair a b c e d \<and> ang_eq B G H a b c \<and> ang_eq G H D e b d" sorry
	have "linear_pair a b c e d" using `linear_pair a b c e d \<and> ang_eq B G H a b c \<and> ang_eq G H D e b d` by blast
	have "ang_eq B G H a b c" using `linear_pair a b c e d \<and> ang_eq B G H a b c \<and> ang_eq G H D e b d` by blast
	have "ang_eq G H D e b d" using `linear_pair a b c e d \<and> ang_eq B G H a b c \<and> ang_eq G H D e b d` by blast
	have "ang_eq a b c B G H" using equalanglessymmetric[OF `axioms` `ang_eq B G H a b c`] .
	have "G \<noteq> H" using angledistinct[OF `axioms` `ang_eq B G H a b c`] by blast
	have "ang_eq e b d G H D" using equalanglessymmetric[OF `axioms` `ang_eq G H D e b d`] .
	have "H = H" using equalityreflexiveE[OF `axioms`] .
	have "ray_on G H H" using ray4 `axioms` `H = H` `G \<noteq> H` by blast
	have "linear_pair A G H H B" sorry
	have "linear_pair B G H H A" using supplementsymmetric[OF `axioms` `linear_pair A G H H B`] .
	have "ang_eq e b d H G A" using supplements[OF `axioms` `ang_eq a b c B G H` `linear_pair a b c e d` `linear_pair B G H H A`] .
	have "ang_eq G H D e b d" using equalanglessymmetric[OF `axioms` `ang_eq e b d G H D`] .
	have "ang_eq G H D H G A" using equalanglestransitive[OF `axioms` `ang_eq G H D e b d` `ang_eq e b d H G A`] .
	have "\<not> col H G A" using equalanglesNC[OF `axioms` `ang_eq G H D H G A`] .
	have "ang_eq H G A A G H" using ABCequalsCBA[OF `axioms` `\<not> col H G A`] .
	have "ang_eq G H D A G H" using equalanglestransitive[OF `axioms` `ang_eq G H D H G A` `ang_eq H G A A G H`] .
	have "ang_eq A G H G H D" using equalanglessymmetric[OF `axioms` `ang_eq G H D A G H`] .
	have "G = G" using equalityreflexiveE[OF `axioms`] .
	have "col G H G" using col_b `axioms` `G = G` by blast
	have "\<not> col A G H" using equalanglesNC[OF `axioms` `ang_eq G H D A G H`] .
	have "\<not> (col G H A)"
	proof (rule ccontr)
		assume "col G H A"
		have "col A G H" using collinearorder[OF `axioms` `col G H A`] by blast
		show "False" using `col A G H` `\<not> col A G H` by blast
	qed
	hence "\<not> col G H A" by blast
	have "oppo_side A G H B" sorry
	have "oppo_side B G H A" using oppositesidesymmetric[OF `axioms` `oppo_side A G H B`] .
	have "oppo_side D G H A" using planeseparation[OF `axioms` `same_side D B G H` `oppo_side B G H A`] .
	have "oppo_side A G H D" using oppositesidesymmetric[OF `axioms` `oppo_side D G H A`] .
	have "parallel A B C D" using Prop27[OF `axioms` `bet A G B` `bet C H D` `ang_eq A G H G H D` `oppo_side A G H D`] .
	thus ?thesis by blast
qed

end