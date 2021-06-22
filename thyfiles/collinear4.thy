theory collinear4
	imports Axioms Definitions Theorems
begin

theorem collinear4:
	assumes: `axioms`
		"col A B C"
		"col A B D"
		"A \<noteq> B"
	shows: "col B C D"
proof -
	consider "B = C"|"B = D"|"C = D"|"A = C"|"A = D"|"B \<noteq> C \<and> B \<noteq> D \<and> C \<noteq> D \<and> A \<noteq> C \<and> A \<noteq> D" by blast
	hence col B C D
	proof (cases)
		case 1
		have "col B C D" using collinear_b `axioms` `B = C` by blast
	next
		case 2
		have "col B C D" using collinear_b `axioms` `B = D` by blast
	next
		case 3
		have "col B C D" using collinear_b `axioms` `C = D` by blast
	next
		case 4
		have "col A B D" using `col A B D` .
		have "col C B D" using `col A B D` `A = C` by blast
		have "col B C D" using collinearorder[OF `axioms` `col C B D`] by blast
	next
		case 5
		have "col A B C" using `col A B C` .
		have "col D B C" using `col A B C` `A = D` by blast
		have "col B C D" using collinearorder[OF `axioms` `col D B C`] by blast
	next
		case 6
		have "B \<noteq> C" using `B \<noteq> C \<and> B \<noteq> D \<and> C \<noteq> D \<and> A \<noteq> C \<and> A \<noteq> D` by blast
		have "B \<noteq> D" using `B \<noteq> C \<and> B \<noteq> D \<and> C \<noteq> D \<and> A \<noteq> C \<and> A \<noteq> D` by blast
		have "A \<noteq> C" using `B \<noteq> C \<and> B \<noteq> D \<and> C \<noteq> D \<and> A \<noteq> C \<and> A \<noteq> D` by blast
		have "A \<noteq> D" using `B \<noteq> C \<and> B \<noteq> D \<and> C \<noteq> D \<and> A \<noteq> C \<and> A \<noteq> D` by blast
		have "A = B \<or> A = C \<or> B = C \<or> bet B A C \<or> bet A B C \<or> bet A C B" using collinear_f[OF `axioms` `col A B C`] .
		have "bet B A C \<or> bet A B C \<or> bet A C B" using `A = B \<or> A = C \<or> B = C \<or> bet B A C \<or> bet A B C \<or> bet A C B` `A \<noteq> B` `B \<noteq> C \<and> B \<noteq> D \<and> C \<noteq> D \<and> A \<noteq> C \<and> A \<noteq> D` `B \<noteq> C \<and> B \<noteq> D \<and> C \<noteq> D \<and> A \<noteq> C \<and> A \<noteq> D` by blast
		consider "bet B A C"|"bet A B C"|"bet A C B" using `bet B A C \<or> bet A B C \<or> bet A C B`  by blast
		hence col B C D
		proof (cases)
			case 1
			have "col A B D" using `col A B D` .
			have "A = B \<or> A = D \<or> B = D \<or> bet B A D \<or> bet A B D \<or> bet A D B" using collinear_f[OF `axioms` `col A B D`] .
			have "bet B A D \<or> bet A B D \<or> bet A D B" using `A = B \<or> A = D \<or> B = D \<or> bet B A D \<or> bet A B D \<or> bet A D B` `A \<noteq> B` `B \<noteq> C \<and> B \<noteq> D \<and> C \<noteq> D \<and> A \<noteq> C \<and> A \<noteq> D` `B \<noteq> C \<and> B \<noteq> D \<and> C \<noteq> D \<and> A \<noteq> C \<and> A \<noteq> D` by blast
			consider "bet B A D"|"bet A B D"|"bet A D B" using `bet B A D \<or> bet A B D \<or> bet A D B`  by blast
			hence col B C D
			proof (cases)
				case 1
				have "\<not> (\<not> col B C D)"
				proof (rule ccontr)
					assume "\<not> col B C D"
					have "\<not> (bet B C D)"
					proof (rule ccontr)
						assume "bet B C D"
						have "col B C D" using collinear_b `axioms` `bet B C D` by blast
						show "False" using `col B C D` `\<not> col B C D` by blast
					qed
					hence "\<not> (bet B C D)" by blast
					have "\<not> (bet A C D)"
					proof (rule ccontr)
						assume "bet A C D"
						have "bet B C D" using n3_5b[OF `axioms` `bet B A D` `bet A C D`] .
						show "False" using `bet B C D` `\<not> (bet B C D)` by blast
					qed
					hence "\<not> (bet A C D)" by blast
					have "\<not> (\<not> col B D C)"
					proof (rule ccontr)
						assume "\<not> col B D C"
						have "\<not> (bet A D C)"
						proof (rule ccontr)
							assume "bet A D C"
							have "bet B D C" using n3_5b[OF `axioms` `bet B A C` `bet A D C`] .
							have "col B D C" using collinear_b `axioms` `bet B D C` by blast
							have "\<not> col B D C" using `\<not> col B D C` .
							show "False" using `\<not> col B D C` `col B D C` by blast
						qed
						hence "\<not> (bet A D C)" by blast
						have "C = D" using outerconnectivity[OF `axioms` `bet B A C` `bet B A D` `\<not> (bet A C D)` `\<not> (bet A D C)`] .
						have "col B C D" using collinear_b `axioms` `C = D` by blast
						have "col B D C" using collinearorder[OF `axioms` `col B C D`] by blast
						show "False" using `col B D C` `\<not> col B D C` by blast
					qed
					hence "col B D C" by blast
					have "col B C D" using collinearorder[OF `axioms` `col B D C`] by blast
					show "False" using `col B C D` `\<not> col B C D` by blast
				qed
				hence "col B C D" by blast
			next
				case 2
				have "bet D B A" using betweennesssymmetryE[OF `axioms` `bet A B D`] .
				have "bet D B C" using n3_7b[OF `axioms` `bet D B A` `bet B A C`] .
				have "col D B C" using collinear_b `axioms` `bet D B C` by blast
				have "col B C D" using collinearorder[OF `axioms` `col D B C`] by blast
			next
				case 3
				have "bet B D A" using betweennesssymmetryE[OF `axioms` `bet A D B`] .
				have "bet B A C" using `bet B A C` .
				have "bet B D C" using n3_6b[OF `axioms` `bet B D A` `bet B A C`] .
				have "col B D C" using collinear_b `axioms` `bet B D C` by blast
				have "col B C D" using collinearorder[OF `axioms` `col B D C`] by blast
			next
		next
			case 2
			have "col A B D" using `col A B D` .
			have "A = B \<or> A = D \<or> B = D \<or> bet B A D \<or> bet A B D \<or> bet A D B" using collinear_f[OF `axioms` `col A B D`] .
			have "bet B A D \<or> bet A B D \<or> bet A D B" using `A = B \<or> A = D \<or> B = D \<or> bet B A D \<or> bet A B D \<or> bet A D B` `A \<noteq> B` `B \<noteq> C \<and> B \<noteq> D \<and> C \<noteq> D \<and> A \<noteq> C \<and> A \<noteq> D` `B \<noteq> C \<and> B \<noteq> D \<and> C \<noteq> D \<and> A \<noteq> C \<and> A \<noteq> D` by blast
			consider "bet B A D"|"bet A B D"|"bet A D B" using `bet B A D \<or> bet A B D \<or> bet A D B`  by blast
			hence col B C D
			proof (cases)
				case 1
				have "bet D A B" using betweennesssymmetryE[OF `axioms` `bet B A D`] .
				have "bet D B C" using n3_7a[OF `axioms` `bet D A B` `bet A B C`] .
				have "col D B C" using collinear_b `axioms` `bet D B C` by blast
				have "col B C D" using collinearorder[OF `axioms` `col D B C`] by blast
			next
				case 2
				have "\<not> (\<not> col B C D)"
				proof (rule ccontr)
					assume "\<not> col B C D"
					have "\<not> (bet B C D)"
					proof (rule ccontr)
						assume "bet B C D"
						have "col B C D" using collinear_b `axioms` `bet B C D` by blast
						show "False" using `col B C D` `\<not> col B C D` by blast
					qed
					hence "\<not> (bet B C D)" by blast
					have "\<not> (bet B D C)"
					proof (rule ccontr)
						assume "bet B D C"
						have "col B D C" using collinear_b `axioms` `bet B D C` by blast
						have "col B C D" using collinearorder[OF `axioms` `col B D C`] by blast
						have "\<not> col B C D" using `\<not> col B C D` .
						show "False" using `\<not> col B C D` `col B C D` by blast
					qed
					hence "\<not> (bet B D C)" by blast
					have "C = D" using outerconnectivity[OF `axioms` `bet A B C` `bet A B D` `\<not> (bet B C D)` `\<not> (bet B D C)`] .
					have "col B C D" using collinear_b `axioms` `C = D` by blast
					show "False" using `col B C D` `\<not> col B C D` by blast
				qed
				hence "col B C D" by blast
			next
				case 3
				have "bet D B C" using n3_6a[OF `axioms` `bet A D B` `bet A B C`] .
				have "col D B C" using collinear_b `axioms` `bet D B C` by blast
				have "col B C D" using collinearorder[OF `axioms` `col D B C`] by blast
			next
		next
			case 3
			have "col A B D" using `col A B D` .
			have "A = B \<or> A = D \<or> B = D \<or> bet B A D \<or> bet A B D \<or> bet A D B" using collinear_f[OF `axioms` `col A B D`] .
			have "bet B A D \<or> bet A B D \<or> bet A D B" using `A = B \<or> A = D \<or> B = D \<or> bet B A D \<or> bet A B D \<or> bet A D B` `A \<noteq> B` `B \<noteq> C \<and> B \<noteq> D \<and> C \<noteq> D \<and> A \<noteq> C \<and> A \<noteq> D` `B \<noteq> C \<and> B \<noteq> D \<and> C \<noteq> D \<and> A \<noteq> C \<and> A \<noteq> D` by blast
			consider "bet B A D"|"bet A B D"|"bet A D B" using `bet B A D \<or> bet A B D \<or> bet A D B`  by blast
			hence col B C D
			proof (cases)
				case 1
				have "bet D A B" using betweennesssymmetryE[OF `axioms` `bet B A D`] .
				have "bet D C B" using n3_5b[OF `axioms` `bet D A B` `bet A C B`] .
				have "bet B C D" using betweennesssymmetryE[OF `axioms` `bet D C B`] .
				have "col B C D" using collinear_b `axioms` `bet B C D` by blast
			next
				case 2
				have "bet A C B" using `bet A C B` .
				have "bet C B D" using n3_6a[OF `axioms` `bet A C B` `bet A B D`] .
				have "col B C D" using collinear_b `axioms` `bet C B D` by blast
			next
				case 3
				have "\<not> (\<not> col B C D)"
				proof (rule ccontr)
					assume "\<not> col B C D"
					have "bet B D C"
					proof (rule ccontr)
						assume "\<not> (bet B D C)"
						have "bet B C D"
						proof (rule ccontr)
							assume "\<not> (bet B C D)"
							have "bet B C A" using betweennesssymmetryE[OF `axioms` `bet A C B`] .
							have "bet B D A" using betweennesssymmetryE[OF `axioms` `bet A D B`] .
							have "C = D" using connectivityE[OF `axioms` `bet B C A` `bet B D A` `\<not> (bet B C D)` `\<not> (bet B D C)`] .
							have "C \<noteq> D" using `B \<noteq> C \<and> B \<noteq> D \<and> C \<noteq> D \<and> A \<noteq> C \<and> A \<noteq> D` by blast
							show "False" using `C \<noteq> D` `C = D` by blast
						qed
						hence "bet B C D" by blast
						have "col B C D" using collinear_b `axioms` `bet B C D` by blast
						show "False" using `col B C D` `\<not> col B C D` by blast
					qed
					hence "bet B D C" by blast
					have "col B D C" using collinear_b `axioms` `bet B D C` by blast
					have "col B C D" using collinearorder[OF `axioms` `col B D C`] by blast
					show "False" using `col B C D` `\<not> col B C D` by blast
				qed
				hence "col B C D" by blast
			next
		next
	next
	thus ?thesis by blast
qed

end