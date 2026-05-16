<?php

use Illuminate\Database\Migrations\Migration;
use Illuminate\Database\Schema\Blueprint;
use Illuminate\Support\Facades\Schema;

return new class extends Migration
{
    /**
     * Run the migrations.
     */
    public function up(): void
    {
        if(!Schema::hasTable('email_activity_logs'))
        {
        Schema::create('email_activity_logs', function (Blueprint $table) {
            $table->id('email_id');
            $table-> string('email_type')->nullable();
            $table->string('email');
            $table->string('subject');
            $table->text('body');
            $table->string('type');
            $table->string('status'); // e.g., 'sent', 'failed'
            $table->timestamp('sent_at')->nullable();
            $table->timestamps();
        });
        }
    }

    /**
     * Reverse the migrations.
     */
    public function down(): void
    {
        Schema::dropIfExists('email_activity_logs');
    }
};
