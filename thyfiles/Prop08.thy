theory Prop08
	imports Geometry collinearorder congruenceflip inequalitysymmetric ray4
begin

theorem(in euclidean_geometry) Prop08:
	assumes 
		"triangle A B C"
		"triangle D E F"
		"seg_eq A B D E"
		"seg_eq A C D F"
		"seg_eq B C E F"
	shows "ang_eq B A C E D F \<and> ang_eq C B A F E D \<and> ang_eq A C B D F E"
proof -
	have "E = E" using equalityreflexiveE.
	have "F = F" using equalityreflexiveE.
	have "B = B" using equalityreflexiveE.
	have "C = C" using equalityreflexiveE.
	have "D = D" using equalityreflexiveE.
	have "A = A" using equalityreflexiveE.
	have "\<not> col A B C" using triangle_f[OF `triangle A B C`] .
	have "\<not> col D E F" using triangle_f[OF `triangle D E F`] .
	have "\<not> (A = B)"
	proof (rule ccontr)
		assume "\<not> (A \<noteq> B)"
		hence "A = B" by blast
		have "col A B C" using collinear_b `A = B` by blast
		show "False" using `col A B C` `\<not> col A B C` by blast
	qed
	hence "A \<noteq> B" by blast
	have "B \<noteq> A" using inequalitysymmetric[OF `A \<noteq> B`] .
	have "\<not> (B = C)"
	proof (rule ccontr)
		assume "\<not> (B \<noteq> C)"
		hence "B = C" by blast
		have "col A B C" using collinear_b `B = C` by blast
		show "False" using `col A B C` `\<not> col A B C` by blast
	qed
	hence "B \<noteq> C" by blast
	have "C \<noteq> B" using inequalitysymmetric[OF `B \<noteq> C`] .
	have "\<not> (D = E)"
	proof (rule ccontr)
		assume "\<not> (D \<noteq> E)"
		hence "D = E" by blast
		have "col D E F" using collinear_b `D = E` by blast
		show "False" using `col D E F` `\<not> col D E F` by blast
	qed
	hence "D \<noteq> E" by blast
	have "E \<noteq> D" using inequalitysymmetric[OF `D \<noteq> E`] .
	have "\<not> (A = C)"
	proof (rule ccontr)
		assume "\<not> (A \<noteq> C)"
		hence "A = C" by blast
		have "col A B C" using collinear_b `A = C` by blast
		show "False" using `col A B C` `\<not> col A B C` by blast
	qed
	hence "A \<noteq> C" by blast
	have "C \<noteq> A" using inequalitysymmetric[OF `A \<noteq> C`] .
	have "\<not> (D = F)"
	proof (rule ccontr)
		assume "\<not> (D \<noteq> F)"
		hence "D = F" by blast
		have "col D E F" using collinear_b `D = F` by blast
		show "False" using `col D E F` `\<not> col D E F` by blast
	qed
	hence "D \<noteq> F" by blast
	have "F \<noteq> D" using inequalitysymmetric[OF `D \<noteq> F`] .
	have "\<not> (E = F)"
	proof (rule ccontr)
		assume "\<not> (E \<noteq> F)"
		hence "E = F" by blast
		have "col D E F" using collinear_b `E = F` by blast
		show "False" using `col D E F` `\<not> col D E F` by blast
	qed
	hence "E \<noteq> F" by blast
	have "F \<noteq> E" using inequalitysymmetric[OF `E \<noteq> F`] .
	have "ray_on D E E" using ray4 `E = E` `D \<noteq> E` by blast
	have "ray_on D F F" using ray4 `F = F` `D \<noteq> F` by blast
	have "ray_on A B B" using ray4 `B = B` `A \<noteq> B` by blast
	have "ray_on A C C" using ray4 `C = C` `A \<noteq> C` by blast
	have "\<not> (col B A C)"
	proof (rule ccontr)
		assume "\<not> (\<not> (col B A C))"
hence "col B A C" by blast
		have "col A B C" using collinearorder[OF `col B A C`] by blast
		show "False" using `col A B C` `\<not> col A B C` by blast
	qed
	hence "\<not> col B A C" by blast
	have "ang_eq B A C E D F" using equalangles_b[OF `ray_on A B B` `ray_on A C C` `ray_on D E E` `ray_on D F F` `seg_eq A B D E` `seg_eq A C D F` `seg_eq B C E F` `\<not> col B A C`] .
	have "seg_eq B C E F" using `seg_eq B C E F` .
	have "seg_eq B A E D" using congruenceflip[OF `seg_eq A B D E`] by blast
	have "seg_eq C A F D" using congruenceflip[OF `seg_eq A C D F`] by blast
	have "ray_on E F F" using ray4 `F = F` `E \<noteq> F` by blast
	have "ray_on E D D" using ray4 `D = D` `E \<noteq> D` by blast
	have "ray_on B C C" using ray4 `C = C` `B \<noteq> C` by blast
	have "ray_on B A A" using ray4 `A = A` `B \<noteq> A` by blast
	have "\<not> (col C B A)"
	proof (rule ccontr)
		assume "\<not> (\<not> (col C B A))"
hence "col C B A" by blast
		have "col A B C" using collinearorder[OF `col C B A`] by blast
		show "False" using `col A B C` `\<not> col A B C` by blast
	qed
	hence "\<not> col C B A" by blast
	have "ang_eq C B A F E D" using equalangles_b[OF `ray_on B C C` `ray_on B A A` `ray_on E F F` `ray_on E D D` `seg_eq B C E F` `seg_eq B A E D` `seg_eq C A F D` `\<not> col C B A`] .
	have "seg_eq C A F D" using congruenceflip[OF `seg_eq A C D F`] by blast
	have "seg_eq C B F E" using congruenceflip[OF `seg_eq B C E F`] by blast
	have "seg_eq A B D E" using `seg_eq A B D E` .
	have "ray_on F D D" using ray4 `D = D` `F \<noteq> D` by blast
	have "ray_on F E E" using ray4 `E = E` `F \<noteq> E` by blast
	have "ray_on C A A" using ray4 `A = A` `C \<noteq> A` by blast
	have "ray_on C B B" using ray4 `B = B` `C \<noteq> B` by blast
	have "\<not> (col A C B)"
	proof (rule ccontr)
		assume "\<not> (\<not> (col A C B))"
hence "col A C B" by blast
		have "col A B C" using collinearorder[OF `col A C B`] by blast
		show "False" using `col A B C` `\<not> col A B C` by blast
	qed
	hence "\<not> col A C B" by blast
	have "ang_eq A C B D F E" using equalangles_b[OF `ray_on C A A` `ray_on C B B` `ray_on F D D` `ray_on F E E` `seg_eq C A F D` `seg_eq C B F E` `seg_eq A B D E` `\<not> col A C B`] .
	have "ang_eq B A C E D F \<and> ang_eq C B A F E D \<and> ang_eq A C B D F E" using `ang_eq B A C E D F` `ang_eq C B A F E D` `ang_eq A C B D F E` by blast
	thus ?thesis by blast
qed

end