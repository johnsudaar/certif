
public class Arith {
	public int mul(int a, int b){
		int res = 0;
		if(b < 0){
			for(int i = -1; i >= b; i--){
				res = sub(res,a);
			}
		} else {
			for(int i = 1; i <= b; i++){
				res = add(res,a);
			}
		}

		return res;
	}
	
	public int srt(int a){
		int res = 0;
		while(mul(res,res) <= a){
			res=add(res,1);
		}
		return res - 1;
	}
	
	public int add(int a, int b){
		if(b < 0){
			for(int i = -1; i >= b; i--){
				a--;
			}
		} else {
			for(int i = 1; i <= b; i++){
				a++;
			}
		}
		return a;
	}
	
	public int sub(int a, int b){
		if(b < 0) {
			for(int i = -1; i>=b ; i--){
				a++;
			}
		} else {
			for(int i = 1; i <= b; i++){
				a --;
			}
		}
		return a;
	}
}
