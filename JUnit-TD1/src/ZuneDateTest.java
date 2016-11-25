import static org.junit.Assert.*;

import java.util.Calendar;
import java.util.concurrent.TimeUnit;

import org.junit.Before;
import org.junit.Test;
import org.mockito.Mockito;

public class ZuneDateTest {
	private ZuneDate zd;
	
	@Before
	public void setUp() throws Exception {
		this.zd = new ZuneDate();
	}

	@Test
	public void testObtenirUniteDeTemps() {
		Calendar dateb = new Calendar.Builder().setDate(2000, 1, 1).build();
		Calendar datej1 = new Calendar.Builder().setDate(2000, 1, 2).build();
		assertEquals(this.zd.obtenirUniteDeTemps(TimeUnit.DAYS, dateb, datej1),1);
		assertEquals(this.zd.obtenirUniteDeTemps(TimeUnit.HOURS, dateb, datej1),24);
	}

	@Test
	public void testGet_days_since_origin() {
		Calendar dateb = new Calendar.Builder().setDate(1980, Calendar.JANUARY, 2).build();
		assertEquals(this.zd.get_days_since_origin(dateb),1);
	}

	@Test
	public void testIsLeapYear() {
		assertFalse(zd.IsLeapYear(2013));
		assertTrue(zd.IsLeapYear(2016));
		assertTrue(zd.IsLeapYear(400));
		assertFalse(zd.IsLeapYear(200));
	}

	@Test
	public void testGet_year() {
		assertEquals(this.zd.get_year(0),1980);
		assertEquals(this.zd.get_year(367),1981);
		assertEquals(this.zd.get_year(366),1980);
		assertEquals(this.zd.get_year(800),1982);
	}

}
