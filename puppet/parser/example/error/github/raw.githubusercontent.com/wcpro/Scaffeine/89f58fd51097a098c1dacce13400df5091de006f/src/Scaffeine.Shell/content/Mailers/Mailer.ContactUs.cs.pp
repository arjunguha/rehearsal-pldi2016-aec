namespace $rootnamespace$.Mailers
{
    using System.Net.Mail;
    using Core.Common.Site;
    using Models;

    public partial class Mailer
    {       
        public virtual MailMessage ContactUs(ContactUsModel model)
        {
            var mailMessage = new MailMessage { Subject = "Contact Us" };

            mailMessage.To.Add(Site.Instance.EmailAddress);
            PopulateBody(mailMessage, viewName: "ContactUs");

            return mailMessage;
        }
    }
}