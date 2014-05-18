namespace $rootnamespace$.Controllers.Users
{
    using System.Web.Mvc;

    public partial class UsersController
    {
        public ActionResult Manager(int page = 1, int pageSize = 10)
        {
            var model = UserService.Page(page, pageSize);
            return View(model);
        }

    }
}
