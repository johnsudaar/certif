import static org.junit.Assert.*;

import org.junit.Before;
import org.junit.Test;

public class ArithTest {

	public Arith ar;
	@Before
	public void setUp() throws Exception {
		this.ar = new Arith();
	}

	@Test
	public void testMul() {
		assertEquals(ar.mul(0, 0),0);
		assertEquals(ar.mul(1, 1),1);
		assertEquals(ar.mul(2000, 6), 12000);
		assertEquals(ar.mul(2, 1000000),2000000);
		assertEquals(ar.mul(100, 200),20000);
		assertEquals(ar.mul(-2, 10), -20);
		assertEquals(ar.mul(10, -2), -20);
		assertEquals(ar.mul(-2, -2), 4);
	}

	@Test
	public void testSrt() {
		assertEquals(ar.srt(1),1);
		assertEquals(ar.srt(9),3);
		assertEquals(ar.srt(81),9);
		assertEquals(ar.srt(80),8);
	}

	@Test
	public void testAdd() {
		assertEquals(ar.add(0, 0),0);
		assertEquals(ar.add(0, 1),1);
		assertEquals(ar.add(1, 0), 1);
		assertEquals(ar.add(30, 80), 110);
		assertEquals(ar.add(-2, 2), 0);
		assertEquals(ar.add(2, -2), 0);
		assertEquals(ar.add(-2, -2), -4);
	}

	@Test
	public void testSub() {
		assertEquals(ar.sub(0, 0),0);
		assertEquals(ar.sub(1, 0),1);
		assertEquals(ar.sub(0, 1),-1);
		assertEquals(ar.sub(100,90),10);
		assertEquals(ar.sub(90,100),-10);
		assertEquals(ar.sub(-2, 0), -2);
		assertEquals(ar.sub(0, -2), 2);
		assertEquals(ar.sub(-2, -2), 0);
	}

}
