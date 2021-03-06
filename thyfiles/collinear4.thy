theory collinear4
	imports n3_5b n3_6a n3_6b n3_7a n3_7b Geometry collinearorder outerconnectivity
begin

theorem(in euclidean_geometry) collinear4:
	assumes 
		"col A B C"
		"col A B D"
		"A \<noteq> B"
	shows "col B C D"
proof -
	consider "B = C"|"B = D"|"C = D"|"A = C"|"A = D"|"B \<noteq> C \<and> B \<noteq> D \<and> C \<noteq> D \<and> A \<noteq> C \<and> A \<noteq> D" by blast
	hence "col B C D"
	proof (cases)
		assume "B = C"
		have "col B C D" using collinear_b `B = C` by blast
		thus ?thesis by blast
	next
		assume "B = D"
		have "col B C D" using collinear_b `B = D` by blast
		thus ?thesis by blast
	next
		assume "C = D"
		have "col B C D" using collinear_b `C = D` by blast
		thus ?thesis by blast
	next
		assume "A = C"
		have "col A B D" using `col A B D` .
		have "col C B D" using `col A B D` `A = C` by blast
		have "col B C D" using collinearorder[OF `col C B D`] by blast
		thus ?thesis by blast
	next
		assume "A = D"
		have "col A B C" using `col A B C` .
		have "col D B C" using `col A B C` `A = D` by blast
		have "col B C D" using collinearorder[OF `col D B C`] by blast
		thus ?thesis by blast
	next
		assume "B \<noteq> C \<and> B \<noteq> D \<and> C \<noteq> D \<and> A \<noteq> C \<and> A \<noteq> D"
		have "B \<noteq> C" using `B \<noteq> C \<and> B \<noteq> D \<and> C \<noteq> D \<and> A \<noteq> C \<and> A \<noteq> D` by blast
		have "B \<noteq> D" using `B \<noteq> C \<and> B \<noteq> D \<and> C \<noteq> D \<and> A \<noteq> C \<and> A \<noteq> D` by blast
		have "A \<noteq> C" using `B \<noteq> C \<and> B \<noteq> D \<and> C \<noteq> D \<and> A \<noteq> C \<and> A \<noteq> D` by blast
		have "A \<noteq> D" using `B \<noteq> C \<and> B \<noteq> D \<and> C \<noteq> D \<and> A \<noteq> C \<and> A \<noteq> D` by blast
		have "A = B \<or> A = C \<or> B = C \<or> bet B A C \<or> bet A B C \<or> bet A C B" using collinear_f[OF `col A B C`] .
		have "bet B A C \<or> bet A B C \<or> bet A C B" using `A = B \<or> A = C \<or> B = C \<or> bet B A C \<or> bet A B C \<or> bet A C B` `A \<noteq> B` `B \<noteq> C \<and> B \<noteq> D \<and> C \<noteq> D \<and> A \<noteq> C \<and> A \<noteq> D` `B \<noteq> C \<and> B \<noteq> D \<and> C \<noteq> D \<and> A \<noteq> C \<and> A \<noteq> D` by blast
		consider "bet B A C"|"bet A B C"|"bet A C B" using `bet B A C \<or> bet A B C \<or> bet A C B`  by blast
		hence "col B C D"
		proof (cases)
			assume "bet B A C"
			have "col A B D" using `col A B D` .
			have "A = B \<or> A = D \<or> B = D \<or> bet B A D \<or> bet A B D \<or> bet A D B" using collinear_f[OF `col A B D`] .
			have "bet B A D \<or> bet A B D \<or> bet A D B" using `A = B \<or> A = D \<or> B = D \<or> bet B A D \<or> bet A B D \<or> bet A D B` `A \<noteq> B` `B \<noteq> C \<and> B \<noteq> D \<and> C \<noteq> D \<and> A \<noteq> C \<and> A \<noteq> D` `B \<noteq> C \<and> B \<noteq> D \<and> C \<noteq> D \<and> A \<noteq> C \<and> A \<noteq> D` by blast
			consider "bet B A D"|"bet A B D"|"bet A D B" using `bet B A D \<or> bet A B D \<or> bet A D B`  by blast
			hence "col B C D"
			proof (cases)
				assume "bet B A D"
				have "\<not> (\<not> col B C D)"
				proof (rule ccontr)
					assume "\<not> (\<not> (\<not> col B C D))"
hence "\<not> col B C D" by blast
					have "\<not> (bet B C D)"
					proof (rule ccontr)
						assume "\<not> (\<not> (bet B C D))"
hence "bet B C D" by blast
						have "col B C D" using collinear_b `bet B C D` by blast
						show "False" using `col B C D` `\<not> col B C D` by blast
					qed
					hence "\<not> (bet B C D)" by blast
					have "\<not> (bet A C D)"
					proof (rule ccontr)
						assume "\<not> (\<not> (bet A C D))"
hence "bet A C D" by blast
						have "bet B C D" using n3_5b[OF `bet B A D` `bet A C D`] .
						show "False" using `bet B C D` `\<not> (bet B C D)` by blast
					qed
					hence "\<not> (bet A C D)" by blast
					have "\<not> (\<not> col B D C)"
					proof (rule ccontr)
						assume "\<not> (\<not> (\<not> col B D C))"
hence "\<not> col B D C" by blast
						have "\<not> (bet A D C)"
						proof (rule ccontr)
							assume "\<not> (\<not> (bet A D C))"
hence "bet A D C" by blast
							have "bet B D C" using n3_5b[OF `bet B A C` `bet A D C`] .
							have "col B D C" using collinear_b `bet B D C` by blast
							have "\<not> col B D C" using `\<not> col B D C` .
							show "False" using `\<not> col B D C` `col B D C` by blast
						qed
						hence "\<not> (bet A D C)" by blast
						have "C = D" using outerconnectivity[OF `bet B A C` `bet B A D` `\<not> (bet A C D)` `\<not> (bet A D C)`] .
						have "col B C D" using collinear_b `C = D` by blast
						have "col B D C" using collinearorder[OF `col B C D`] by blast
						show "False" using `col B D C` `\<not> col B D C` by blast
					qed
					hence "col B D C" by blast
					have "col B C D" using collinearorder[OF `col B D C`] by blast
					show "False" using `col B C D` `\<not> col B C D` by blast
				qed
				hence "col B C D" by blast
				thus ?thesis by blast
			next
				assume "bet A B D"
				have "bet D B A" using betweennesssymmetryE[OF `bet A B D`] .
				have "bet D B C" using n3_7b[OF `bet D B A` `bet B A C`] .
				have "col D B C" using collinear_b `bet D B C` by blast
				have "col B C D" using collinearorder[OF `col D B C`] by blast
				thus ?thesis by blast
			next
				assume "bet A D B"
				have "bet B D A" using betweennesssymmetryE[OF `bet A D B`] .
				have "bet B A C" using `bet B A C` .
				have "bet B D C" using n3_6b[OF `bet B D A` `bet B A C`] .
				have "col B D C" using collinear_b `bet B D C` by blast
				have "col B C D" using collinearorder[OF `col B D C`] by blast
				thus ?thesis by blast
			qed
			thus ?thesis by blast
		next
			assume "bet A B C"
			have "col A B D" using `col A B D` .
			have "A = B \<or> A = D \<or> B = D \<or> bet B A D \<or> bet A B D \<or> bet A D B" using collinear_f[OF `col A B D`] .
			have "bet B A D \<or> bet A B D \<or> bet A D B" using `A = B \<or> A = D \<or> B = D \<or> bet B A D \<or> bet A B D \<or> bet A D B` `A \<noteq> B` `B \<noteq> C \<and> B \<noteq> D \<and> C \<noteq> D \<and> A \<noteq> C \<and> A \<noteq> D` `B \<noteq> C \<and> B \<noteq> D \<and> C \<noteq> D \<and> A \<noteq> C \<and> A \<noteq> D` by blast
			consider "bet B A D"|"bet A B D"|"bet A D B" using `bet B A D \<or> bet A B D \<or> bet A D B`  by blast
			hence "col B C D"
			proof (cases)
				assume "bet B A D"
				have "bet D A B" using betweennesssymmetryE[OF `bet B A D`] .
				have "bet D B C" using n3_7a[OF `bet D A B` `bet A B C`] .
				have "col D B C" using collinear_b `bet D B C` by blast
				have "col B C D" using collinearorder[OF `col D B C`] by blast
				thus ?thesis by blast
			next
				assume "bet A B D"
				have "\<not> (\<not> col B C D)"
				proof (rule ccontr)
					assume "\<not> (\<not> (\<not> col B C D))"
hence "\<not> col B C D" by blast
					have "\<not> (bet B C D)"
					proof (rule ccontr)
						assume "\<not> (\<not> (bet B C D))"
hence "bet B C D" by blast
						have "col B C D" using collinear_b `bet B C D` by blast
						show "False" using `col B C D` `\<not> col B C D` by blast
					qed
					hence "\<not> (bet B C D)" by blast
					have "\<not> (bet B D C)"
					proof (rule ccontr)
						assume "\<not> (\<not> (bet B D C))"
hence "bet B D C" by blast
						have "col B D C" using collinear_b `bet B D C` by blast
						have "col B C D" using collinearorder[OF `col B D C`] by blast
						have "\<not> col B C D" using `\<not> col B C D` .
						show "False" using `\<not> col B C D` `col B C D` by blast
					qed
					hence "\<not> (bet B D C)" by blast
					have "C = D" using outerconnectivity[OF `bet A B C` `bet A B D` `\<not> (bet B C D)` `\<not> (bet B D C)`] .
					have "col B C D" using collinear_b `C = D` by blast
					show "False" using `col B C D` `\<not> col B C D` by blast
				qed
				hence "col B C D" by blast
				thus ?thesis by blast
			next
				assume "bet A D B"
				have "bet D B C" using n3_6a[OF `bet A D B` `bet A B C`] .
				have "col D B C" using collinear_b `bet D B C` by blast
				have "col B C D" using collinearorder[OF `col D B C`] by blast
				thus ?thesis by blast
			qed
			thus ?thesis by blast
		next
			assume "bet A C B"
			have "col A B D" using `col A B D` .
			have "A = B \<or> A = D \<or> B = D \<or> bet B A D \<or> bet A B D \<or> bet A D B" using collinear_f[OF `col A B D`] .
			have "bet B A D \<or> bet A B D \<or> bet A D B" using `A = B \<or> A = D \<or> B = D \<or> bet B A D \<or> bet A B D \<or> bet A D B` `A \<noteq> B` `B \<noteq> C \<and> B \<noteq> D \<and> C \<noteq> D \<and> A \<noteq> C \<and> A \<noteq> D` `B \<noteq> C \<and> B \<noteq> D \<and> C \<noteq> D \<and> A \<noteq> C \<and> A \<noteq> D` by blast
			consider "bet B A D"|"bet A B D"|"bet A D B" using `bet B A D \<or> bet A B D \<or> bet A D B`  by blast
			hence "col B C D"
			proof (cases)
				assume "bet B A D"
				have "bet D A B" using betweennesssymmetryE[OF `bet B A D`] .
				have "bet D C B" using n3_5b[OF `bet D A B` `bet A C B`] .
				have "bet B C D" using betweennesssymmetryE[OF `bet D C B`] .
				have "col B C D" using collinear_b `bet B C D` by blast
				thus ?thesis by blast
			next
				assume "bet A B D"
				have "bet A C B" using `bet A C B` .
				have "bet C B D" using n3_6a[OF `bet A C B` `bet A B D`] .
				have "col B C D" using collinear_b `bet C B D` by blast
				thus ?thesis by blast
			next
				assume "bet A D B"
				have "\<not> (\<not> col B C D)"
				proof (rule ccontr)
					assume "\<not> (\<not> (\<not> col B C D))"
hence "\<not> col B C D" by blast
					have "\<not> (\<not> (bet B D C))"
					proof (rule ccontr)
						assume "\<not> (\<not> (\<not> (bet B D C)))"
hence "\<not> (bet B D C)" by blast
						have "\<not> (\<not> (bet B C D))"
						proof (rule ccontr)
							assume "\<not> (\<not> (\<not> (bet B C D)))"
hence "\<not> (bet B C D)" by blast
							have "bet B C A" using betweennesssymmetryE[OF `bet A C B`] .
							have "bet B D A" using betweennesssymmetryE[OF `bet A D B`] .
							have "C = D" using connectivityE[OF `bet B C A` `bet B D A` `\<not> (bet B C D)` `\<not> (bet B D C)`] .
							have "C \<noteq> D" using `B \<noteq> C \<and> B \<noteq> D \<and> C \<noteq> D \<and> A \<noteq> C \<and> A \<noteq> D` by blast
							show "False" using `C \<noteq> D` `C = D` by blast
						qed
						hence "bet B C D" by blast
						have "col B C D" using collinear_b `bet B C D` by blast
						show "False" using `col B C D` `\<not> col B C D` by blast
					qed
					hence "bet B D C" by blast
					have "col B D C" using collinear_b `bet B D C` by blast
					have "col B C D" using collinearorder[OF `col B D C`] by blast
					show "False" using `col B C D` `\<not> col B C D` by blast
				qed
				hence "col B C D" by blast
				thus ?thesis by blast
			qed
			thus ?thesis by blast
		qed
		thus ?thesis by blast
	qed
	thus ?thesis by blast
qed

end