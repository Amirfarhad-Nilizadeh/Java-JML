public class AbsoluteDriver {
	/*@ spec_public*/ int i;
	/*@ spec_public*/ short sh;
	/*@ spec_public*/ long l;

	//@ requires Short.MIN_VALUE < sh && sh <= Short.MAX_VALUE;
	//@ requires Integer.MIN_VALUE < i && i <= Integer.MAX_VALUE;
	//@ requires Long.MIN_VALUE < l && l <= Long.MAX_VALUE;
	//@ ensures  this.sh == sh && this.i == i && this.l == l;
	public /*@ pure @*/ AbsoluteDriver(short sh, int i, long l) {
		this.sh = sh;
		this.i = i;
		this.l = l;
	}
	
	//@ requires Short.MIN_VALUE < sh && sh <= Short.MAX_VALUE;
	//@ requires Integer.MIN_VALUE < i && i <= Integer.MAX_VALUE;
	//@ requires Long.MIN_VALUE < l && l <= Long.MAX_VALUE;
	//@ assignable this.i, this.sh, this.l;
	//@ ensures 0 <= sh ==> this.sh == sh;
	//@ ensures sh < 0 ==> this.sh == -sh;
	//@ ensures 0 <= i ==> this.i == i;
	//@ ensures i < 0 ==> this.i == -i;
 	//@ ensures 0 <= l ==> this.l == l;
	//@ ensures l < 0 ==> this.l == -l;
	public void driver() {
		Absolute p = new Absolute();
		this.sh = p.Absolute(sh);
		this.i = p.Absolute(i);
		this.l = p.Absolute(l);
	}
}
