import java.util.Calendar;
import java.util.concurrent.TimeUnit;

public class ZuneDate {
	private static final int ORIGINYEAR = 1980;
	
	
	
	public  long obtenirUniteDeTemps(TimeUnit units, Calendar date1, Calendar date2)
  	{	
    	return units.convert(date2.getTimeInMillis() - date1.getTimeInMillis(), TimeUnit.MILLISECONDS);
  	}
 
	public  int get_days_since_origin (Calendar current) {
	 	Calendar cal = (Calendar) current.clone();
	 	Calendar org =  (Calendar) current.clone();
   	        org.set(ORIGINYEAR, Calendar.JANUARY, 1);
	 	return ((int) obtenirUniteDeTemps(TimeUnit.DAYS, org, cal));
	}

	public  Boolean IsLeapYear(int year) {
		if(year % 4 == 0)
		{
			if (year % 100 == 0)
			{
				if(year%400 ==0){
					return true;
				} else {
					return false;
				}
			} else {
				return true;
			}
		} else {
			return false;
		}
	}

	public  int get_year(int days) {
		int year = ORIGINYEAR;
		while (days > 365)
		{
			
			if (IsLeapYear(year))
			{
				if (days > 366)
				{
					days -= 366;
					year += 1;
				} else{
					return year;
				}
			}
			else
			{
				days -= 365;
				year += 1;
			}
		}
		return year;
	}
	
}