theory collinearorder
	imports Geometry collinear1 collinear2
begin

theorem collinearorder:
	assumes "axioms"
		"col A B C"
	shows "col B A C \<and> col B C A \<and> col C A B \<and> col A C B \<and> col C B A"
proof -
	have "col B C A" using collinear2[OF `axioms` `col A B C`] .
	have "col C A B" using collinear2[OF `axioms` `col B C A`] .
	have "col B A C" using collinear1[OF `axioms` `col A B C`] .
	have "col A C B" using collinear2[OF `axioms` `col B A C`] .
	have "col C B A" using collinear2[OF `axioms` `col A C B`] .
	have "col B A C \<and> col B C A \<and> col C A B \<and> col A C B \<and> col C B A" using `col B A C` `col B C A` `col C A B` `col A C B` `col C B A` by blast
	thus ?thesis by blast
qed

end