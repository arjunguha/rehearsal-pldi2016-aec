namespace $rootnamespace$.Filters.UserContextFilters
{
    using System.Web.Mvc;
    using Core.Infrastructure.Pipeline;
    using Core.Model;
    using Extensions;

    public class UpdateSubscriptionFilter : Filter<ActionExecutingContext>
	{
	    public override bool Process(ref ActionExecutingContext data)
	    {
	        if (data.HttpContext.Request.IsAuthenticated)
	        {
	            var user = data.Controller.GetCurrentUser();

                // if password reset is required, redirect to change password page
                if (user.SubscriptionStatus == SubscriptionStatus.Active)
                {
                    data.Controller.TempData["Information"] = "Please fill in your credit card information";
                    data.SafeRedirect("Create", "Subscription");
                    return false;
                }
	            if (user.SubscriptionStatus == SubscriptionStatus.Expired)
	            {
	                data.Controller.TempData["Error"] = "Please update your subscription information";
                    data.SafeRedirect("Create", "Subscription");
	                return false;
	            }
	        }
	        return true;
	    }
	}
}