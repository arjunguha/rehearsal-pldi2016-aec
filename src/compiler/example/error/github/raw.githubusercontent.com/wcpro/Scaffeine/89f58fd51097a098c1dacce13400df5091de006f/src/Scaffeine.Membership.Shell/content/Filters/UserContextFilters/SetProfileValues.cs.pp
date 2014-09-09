namespace $rootnamespace$.Filters.UserContextFilters
{
    using System.Web.Mvc;
    using Core.Infrastructure.Pipeline;
    using Extensions;

    public class SetProfileValues : Filter<ActionExecutingContext>
	{
	    public override bool Process(ref ActionExecutingContext data)
	    {
	        if (data.HttpContext.Request.IsAuthenticated)
            {
                var user = data.Controller.GetCurrentUser();

                if (user == null)
                {
                    return false;
                }
                var vb = data.Controller.ViewBag;
                vb.CurrentUser = user;
            }
	        return true;
	    }
	}
}