theory n8_2
	imports Axioms Definitions Theorems
begin

theorem n8_2:
	assumes: `axioms`
		"ang_right A B C"
	shows: "ang_right C B A"
proof -
	obtain D where "bet A B D \<and> seg_eq A B D B \<and> seg_eq A C D C \<and> B \<noteq> C" using rightangle_f[OF `axioms` `ang_right A B C`] by blast
	have "bet A B D" using `bet A B D \<and> seg_eq A B D B \<and> seg_eq A C D C \<and> B \<noteq> C` by blast
	have "seg_eq A B D B" using `bet A B D \<and> seg_eq A B D B \<and> seg_eq A C D C \<and> B \<noteq> C` by blast
	have "B \<noteq> C" using `bet A B D \<and> seg_eq A B D B \<and> seg_eq A C D C \<and> B \<noteq> C` by blast
	have "C \<noteq> B" using inequalitysymmetric[OF `axioms` `B \<noteq> C`] .
	obtain E where "bet C B E \<and> seg_eq B E B C" using extensionE[OF `axioms` `C \<noteq> B` `B \<noteq> C`] by blast
	have "bet C B E" using `bet C B E \<and> seg_eq B E B C` by blast
	have "seg_eq B E B C" using `bet C B E \<and> seg_eq B E B C` by blast
	have "A \<noteq> B" using betweennotequal[OF `axioms` `bet A B D`] by blast
	have "B \<noteq> A" using inequalitysymmetric[OF `axioms` `A \<noteq> B`] .
	have "C = C" using equalityreflexiveE[OF `axioms`] .
	have "A = A" using equalityreflexiveE[OF `axioms`] .
	have "ray_on B C C" using ray4 `axioms` `C = C` `bet A B D \<and> seg_eq A B D B \<and> seg_eq A C D C \<and> B \<noteq> C` by blast
	have "\<not> col A B C" using rightangleNC[OF `axioms` `ang_right A B C`] .
	have "linear_pair A B C C D" using supplement_b[OF `axioms` `ray_on B C C` `bet A B D`] .
	have "ray_on B A A" using ray4 `axioms` `A = A` `B \<noteq> A` by blast
	have "linear_pair C B A A E" using supplement_b[OF `axioms` `ray_on B A A` `bet C B E`] .
	have "ang_eq A B C C B A" using ABCequalsCBA[OF `axioms` `\<not> col A B C`] .
	have "ang_eq C B D A B E" using supplements[OF `axioms` `ang_eq A B C C B A` `linear_pair A B C C D` `linear_pair C B A A E`] .
	have "seg_eq B C B E" using congruencesymmetric[OF `axioms` `seg_eq B E B C`] .
	have "seg_eq B D B A" using doublereverse[OF `axioms` `seg_eq A B D B`] by blast
	have "\<not> (col E B A)"
	proof (rule ccontr)
		assume "col E B A"
		have "col C B E" using collinear_b `axioms` `bet C B E \<and> seg_eq B E B C` by blast
		have "col E B C" using collinearorder[OF `axioms` `col C B E`] by blast
		have "B \<noteq> E" using betweennotequal[OF `axioms` `bet C B E`] by blast
		have "E \<noteq> B" using inequalitysymmetric[OF `axioms` `B \<noteq> E`] .
		have "col E B A" using `col E B A` .
		have "col B A C" using collinear4[OF `axioms` `col E B A` `col E B C` `E \<noteq> B`] .
		have "col A B C" using collinearorder[OF `axioms` `col B A C`] by blast
		show "False" using `col A B C` `\<not> col A B C` by blast
	qed
	hence "\<not> col E B A" by blast
	have "\<not> (col A B E)"
	proof (rule ccontr)
		assume "col A B E"
		have "col E B A" using collinearorder[OF `axioms` `col A B E`] by blast
		show "False" using `col E B A` `\<not> col E B A` by blast
	qed
	hence "\<not> col A B E" by blast
	have "ang_eq A B E E B A" using ABCequalsCBA[OF `axioms` `\<not> col A B E`] .
	have "ang_eq C B D E B A" using equalanglestransitive[OF `axioms` `ang_eq C B D A B E` `ang_eq A B E E B A`] .
	have "seg_eq C D E A \<and> ang_eq B C D B E A \<and> ang_eq B D C B A E" using Prop04[OF `axioms` `seg_eq B C B E` `seg_eq B D B A` `ang_eq C B D E B A`] .
	have "seg_eq C D E A" using `seg_eq C D E A \<and> ang_eq B C D B E A \<and> ang_eq B D C B A E` by blast
	have "seg_eq A C D C" using `bet A B D \<and> seg_eq A B D B \<and> seg_eq A C D C \<and> B \<noteq> C` by blast
	have "seg_eq A C C D" using congruenceflip[OF `axioms` `seg_eq A C D C`] by blast
	have "seg_eq A C E A" using congruencetransitive[OF `axioms` `seg_eq A C C D` `seg_eq C D E A`] .
	have "seg_eq C A E A" using congruenceflip[OF `axioms` `seg_eq A C E A`] by blast
	have "seg_eq C B E B" using congruenceflip[OF `axioms` `seg_eq B C B E`] by blast
	have "B \<noteq> A" using inequalitysymmetric[OF `axioms` `A \<noteq> B`] .
	have "bet C B E \<and> seg_eq C B E B \<and> seg_eq C A E A \<and> B \<noteq> A" using `bet C B E \<and> seg_eq B E B C` `seg_eq C B E B` `seg_eq C A E A` `B \<noteq> A` by blast
	have "ang_right C B A" using rightangle_b[OF `axioms` `bet C B E` `seg_eq C B E B` `seg_eq C A E A` `B \<noteq> A`] .
	thus ?thesis by blast
qed

end