theory Prop08
	imports Axioms Definitions Theorems
begin

theorem Prop08:
	assumes: `axioms`
		"triangle A B C"
		"triangle D E F"
		"seg_eq A B D E"
		"seg_eq A C D F"
		"seg_eq B C E F"
	shows: "ang_eq B A C E D F \<and> ang_eq C B A F E D \<and> ang_eq A C B D F E"
proof -
	have "E = E" using equalityreflexiveE[OF `axioms`] .
	have "F = F" using equalityreflexiveE[OF `axioms`] .
	have "B = B" using equalityreflexiveE[OF `axioms`] .
	have "C = C" using equalityreflexiveE[OF `axioms`] .
	have "D = D" using equalityreflexiveE[OF `axioms`] .
	have "A = A" using equalityreflexiveE[OF `axioms`] .
	have "\<not> col A B C" using triangle_f[OF `axioms` `triangle A B C`] .
	have "\<not> col D E F" using triangle_f[OF `axioms` `triangle D E F`] .
	have "\<not> (A = B)"
	proof (rule ccontr)
		assume "A = B"
		have "col A B C" using collinear_b `axioms` `A = B` by blast
		show "False" using `col A B C` `\<not> col A B C` by blast
	qed
	hence "A \<noteq> B" by blast
	have "B \<noteq> A" using inequalitysymmetric[OF `axioms` `A \<noteq> B`] .
	have "\<not> (B = C)"
	proof (rule ccontr)
		assume "B = C"
		have "col A B C" using collinear_b `axioms` `B = C` by blast
		show "False" using `col A B C` `\<not> col A B C` by blast
	qed
	hence "B \<noteq> C" by blast
	have "C \<noteq> B" using inequalitysymmetric[OF `axioms` `B \<noteq> C`] .
	have "\<not> (D = E)"
	proof (rule ccontr)
		assume "D = E"
		have "col D E F" using collinear_b `axioms` `D = E` by blast
		show "False" using `col D E F` `\<not> col D E F` by blast
	qed
	hence "D \<noteq> E" by blast
	have "E \<noteq> D" using inequalitysymmetric[OF `axioms` `D \<noteq> E`] .
	have "\<not> (A = C)"
	proof (rule ccontr)
		assume "A = C"
		have "col A B C" using collinear_b `axioms` `A = C` by blast
		show "False" using `col A B C` `\<not> col A B C` by blast
	qed
	hence "A \<noteq> C" by blast
	have "C \<noteq> A" using inequalitysymmetric[OF `axioms` `A \<noteq> C`] .
	have "\<not> (D = F)"
	proof (rule ccontr)
		assume "D = F"
		have "col D E F" using collinear_b `axioms` `D = F` by blast
		show "False" using `col D E F` `\<not> col D E F` by blast
	qed
	hence "D \<noteq> F" by blast
	have "F \<noteq> D" using inequalitysymmetric[OF `axioms` `D \<noteq> F`] .
	have "\<not> (E = F)"
	proof (rule ccontr)
		assume "E = F"
		have "col D E F" using collinear_b `axioms` `E = F` by blast
		show "False" using `col D E F` `\<not> col D E F` by blast
	qed
	hence "E \<noteq> F" by blast
	have "F \<noteq> E" using inequalitysymmetric[OF `axioms` `E \<noteq> F`] .
	have "ray_on D E E" using ray4 `axioms` `E = E` `D \<noteq> E` by blast
	have "ray_on D F F" using ray4 `axioms` `F = F` `D \<noteq> F` by blast
	have "ray_on A B B" using ray4 `axioms` `B = B` `A \<noteq> B` by blast
	have "ray_on A C C" using ray4 `axioms` `C = C` `A \<noteq> C` by blast
	have "\<not> (col B A C)"
	proof (rule ccontr)
		assume "col B A C"
		have "col A B C" using collinearorder[OF `axioms` `col B A C`] by blast
		show "False" using `col A B C` `\<not> col A B C` by blast
	qed
	hence "\<not> col B A C" by blast
	have "ang_eq B A C E D F" using equalangles_b[OF `axioms` `ray_on A B B` `ray_on A C C` `ray_on D E E` `ray_on D F F` `seg_eq A B D E` `seg_eq A C D F` `seg_eq B C E F` `\<not> col B A C`] .
	have "seg_eq B C E F" using `seg_eq B C E F` .
	have "seg_eq B A E D" using congruenceflip[OF `axioms` `seg_eq A B D E`] by blast
	have "seg_eq C A F D" using congruenceflip[OF `axioms` `seg_eq A C D F`] by blast
	have "ray_on E F F" using ray4 `axioms` `F = F` `E \<noteq> F` by blast
	have "ray_on E D D" using ray4 `axioms` `D = D` `E \<noteq> D` by blast
	have "ray_on B C C" using ray4 `axioms` `C = C` `B \<noteq> C` by blast
	have "ray_on B A A" using ray4 `axioms` `A = A` `B \<noteq> A` by blast
	have "\<not> (col C B A)"
	proof (rule ccontr)
		assume "col C B A"
		have "col A B C" using collinearorder[OF `axioms` `col C B A`] by blast
		show "False" using `col A B C` `\<not> col A B C` by blast
	qed
	hence "\<not> col C B A" by blast
	have "ang_eq C B A F E D" using equalangles_b[OF `axioms` `ray_on B C C` `ray_on B A A` `ray_on E F F` `ray_on E D D` `seg_eq B C E F` `seg_eq B A E D` `seg_eq C A F D` `\<not> col C B A`] .
	have "seg_eq C A F D" using congruenceflip[OF `axioms` `seg_eq A C D F`] by blast
	have "seg_eq C B F E" using congruenceflip[OF `axioms` `seg_eq B C E F`] by blast
	have "seg_eq A B D E" using `seg_eq A B D E` .
	have "ray_on F D D" using ray4 `axioms` `D = D` `F \<noteq> D` by blast
	have "ray_on F E E" using ray4 `axioms` `E = E` `F \<noteq> E` by blast
	have "ray_on C A A" using ray4 `axioms` `A = A` `C \<noteq> A` by blast
	have "ray_on C B B" using ray4 `axioms` `B = B` `C \<noteq> B` by blast
	have "\<not> (col A C B)"
	proof (rule ccontr)
		assume "col A C B"
		have "col A B C" using collinearorder[OF `axioms` `col A C B`] by blast
		show "False" using `col A B C` `\<not> col A B C` by blast
	qed
	hence "\<not> col A C B" by blast
	have "ang_eq A C B D F E" using equalangles_b[OF `axioms` `ray_on C A A` `ray_on C B B` `ray_on F D D` `ray_on F E E` `seg_eq C A F D` `seg_eq C B F E` `seg_eq A B D E` `\<not> col A C B`] .
	have "ang_eq B A C E D F \<and> ang_eq C B A F E D \<and> ang_eq A C B D F E" using `ang_eq B A C E D F` `ang_eq C B A F E D` `ang_eq A C B D F E` by blast
	thus ?thesis by blast
qed

end