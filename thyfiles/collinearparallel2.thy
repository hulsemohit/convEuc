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
