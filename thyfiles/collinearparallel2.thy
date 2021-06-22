theory collinearparallel2
	imports Axioms Definitions Theorems
begin

theorem collinearparallel2:
	assumes: `axioms`
		"parallel A B C D"
		"col C D E"
		"col C D F"
		"E \<noteq> F"
	shows: "parallel A B E F"
proof -
	have "F \<noteq> E" using inequalitysymmetric[OF `axioms` `E \<noteq> F`] .
	have "\<not> col A C D" using parallelNC[OF `axioms` `parallel A B C D`] by blast
	have "C \<noteq> D" using NCdistinct[OF `axioms` `\<not> col A C D`] by blast
	have "D \<noteq> C" using inequalitysymmetric[OF `axioms` `C \<noteq> D`] .
	have "col D C E" using collinearorder[OF `axioms` `col C D E`] by blast
	have "col D C F" using collinearorder[OF `axioms` `col C D F`] by blast
	have "col C E F" using collinear4[OF `axioms` `col D C E` `col D C F` `D \<noteq> C`] .
	consider "E = D"|"E \<noteq> D" by blast
	hence parallel A B E F
	proof (cases)
		case 1
		have "D \<noteq> F" sorry
		have "F \<noteq> D" using inequalitysymmetric[OF `axioms` `D \<noteq> F`] .
		have "parallel A B C D" using `parallel A B C D` .
		have "parallel A B F D" using collinearparallel[OF `axioms` `parallel A B C D` `col C D F` `F \<noteq> D`] .
		have "parallel A B D F" using parallelflip[OF `axioms` `parallel A B F D`] by blast
		have "col C F D" using collinearorder[OF `axioms` `col C D F`] by blast
		have "col C F E" using collinearorder[OF `axioms` `col C E F`] by blast
		consider "C = F"|"C \<noteq> F" by blast
		hence col F D E
		proof (cases)
			case 1
			have "col C D E" using collinearorder[OF `axioms` `col D C E`] by blast
			have "col F D E" sorry
		next
			case 2
			have "col F D E" using collinear4[OF `axioms` `col C F D` `col C F E` `C \<noteq> F`] .
		next
		have "col D F E" using collinearorder[OF `axioms` `col F D E`] by blast
		have "parallel A B E F" using collinearparallel[OF `axioms` `parallel A B D F` `col D F E` `E \<noteq> F`] .
	next
		case 2
		have "parallel A B C D" using `parallel A B C D` .
		have "parallel A B E D" using collinearparallel[OF `axioms` `parallel A B C D` `col C D E` `E \<noteq> D`] .
		have "parallel A B D E" using parallelflip[OF `axioms` `parallel A B E D`] by blast
		have "col D E F" using collinear4[OF `axioms` `col C D E` `col C D F` `C \<noteq> D`] .
		have "parallel A B F E" using collinearparallel[OF `axioms` `parallel A B D E` `col D E F` `F \<noteq> E`] .
		have "parallel A B E F" using parallelflip[OF `axioms` `parallel A B F E`] by blast
	next
	thus ?thesis by blast
qed

end