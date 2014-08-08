namespace $rootnamespace$.Controllers.Community
{
    using System.Web.Mvc;

    public class CommunityController : Controller
    {
        public ActionResult Index()
        {
            return this.View();
        }
    }
}
